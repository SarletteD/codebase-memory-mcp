/*
 * st_members.c — Structured Text / TwinCAT DUT members in the USAGE resolver.
 *
 * Enum members and struct fields are Field nodes under their Type
 * (extract_defs.c). A member token `E_State.CLOSE` reaches the resolver as the
 * bare name "CLOSE" plus the receiver it hung off (CBMUsage.member_qualifier)
 * and, for a variable receiver, the type its VAR block declares
 * (CBMUsage.qualifier_type). This file turns that into an edge to the exact
 * Field — or into nothing:
 *
 *   E_State.CLOSE            Type E_State           -> Field E_State.CLOSE
 *   Vnd_Core.E_AlarmState.OFF library alias + Type   -> Field E_AlarmState.OFF
 *   _par.Inner.Depth         VAR _par : T_Par       -> Field T_Par.Inner
 *                            -> its return_type T_Inner -> Field T_Inner.Depth
 *
 * Every hop is exact: a bare type name must be the only registered type of
 * that name, or the only one inside the same .plcproj library as the file
 * making the reference (the same rule twincat_ns.c applies to qualified
 * bases); a qualified type name goes through the library alias; a Field is
 * looked up by qualified name under its Type; the next hop resolves the
 * Field's declared type in the FIELD's own file, not the caller's. An unknown
 * member, an unresolvable or ambiguous type, or an index/dereference in the
 * chain yields no edge.
 *
 * DUT members never enter the symbol registry (cbm_st_is_dut_member_qn), so a
 * BARE name — `y := CLOSE` says nothing about which enum — cannot bind one by
 * registry uniqueness in any language, and cannot displace a same-named
 * registered symbol of another language either.
 *
 * The second half aggregates occurrences: one USAGE edge per (source, target)
 * as before, with `line` (first occurrence) and `count` (occurrences in that
 * source node) in its properties. Both resolve venues (pass_usages.c and
 * pass_parallel.c) route every ST usage through cbm_st_resolve_plain +
 * cbm_st_resolve_member + the aggregator, so they cannot diverge.
 */
#include "foundation/constants.h"
#include "foundation/hash_table.h"
#include "foundation/str_util.h"
#include "pipeline/pipeline.h"
#include "pipeline/pipeline_internal.h"
#include "pipeline/lsp_resolve.h"
#include "pipeline/pass_lsp_cross.h"
#include "graph_buffer/graph_buffer.h"
#include "cbm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Dotted receiver chains longer than this are not resolved. */
#define ST_MAX_SEGMENTS 16

bool cbm_st_lang(CBMLanguage lang) {
    return lang == CBM_LANG_ST || lang == CBM_LANG_TWINCAT;
}

/* Value of a top-level string property in a node's JSON, or NULL. Definition
 * properties are written by pass_definitions.c with plain escaping; a type
 * name never carries an escape, so a value holding a backslash is refused. */
static const char *json_string_prop(const char *json, const char *key, char *out, size_t out_size) {
    if (!json || !key) {
        return NULL;
    }
    char needle[CBM_SZ_64];
    snprintf(needle, sizeof(needle), "\"%s\":\"", key);
    const char *p = strstr(json, needle);
    if (!p) {
        return NULL;
    }
    p += strlen(needle);
    const char *end = strchr(p, '"');
    if (!end || (size_t)(end - p) >= out_size || memchr(p, '\\', (size_t)(end - p))) {
        return NULL;
    }
    memcpy(out, p, (size_t)(end - p));
    out[end - p] = '\0';
    return out;
}

/* Parent qualified name of a member node: everything before the last '.'. */
static bool parent_qn_of(const char *qn, char *out, size_t out_size) {
    const char *dot = qn ? strrchr(qn, '.') : NULL;
    if (!dot || dot == qn || (size_t)(dot - qn) >= out_size) {
        return false;
    }
    memcpy(out, qn, (size_t)(dot - qn));
    out[dot - qn] = '\0';
    return true;
}

bool cbm_st_is_dut_member_qn(const cbm_gbuf_t *gbuf, const char *label, const char *qn) {
    if (!gbuf || !label || strcmp(label, "Field") != 0) {
        return false;
    }
    char parent_qn[CBM_SZ_1K];
    if (!parent_qn_of(qn, parent_qn, sizeof(parent_qn))) {
        return false;
    }
    const cbm_gbuf_node_t *parent = cbm_gbuf_find_by_qn(gbuf, parent_qn);
    return parent && parent->label && strcmp(parent->label, "Type") == 0;
}

bool cbm_st_is_dut_member(const cbm_gbuf_t *gbuf, const cbm_gbuf_node_t *tgt) {
    return tgt && cbm_st_is_dut_member_qn(gbuf, tgt->label, tgt->qualified_name);
}

/* A plain type name (`T_Par`, `Vnd_Core.T_Par`): identifier characters and dots
 * only. `ARRAY [0..3] OF X`, `REF_TO X`, `POINTER TO X` are not followed. */
static bool is_plain_type_name(const char *s) {
    if (!s || !s[0]) {
        return false;
    }
    for (const char *p = s; *p; p++) {
        bool ok = (*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') ||
                  (*p >= '0' && *p <= '9') || *p == '_' || *p == '.';
        if (!ok) {
            return false;
        }
    }
    return true;
}

typedef struct {
    cbm_tc_ns_t *ns;
    const cbm_registry_t *reg;
    const cbm_gbuf_t *gbuf;
    CBMLanguage lang;
} st_resolve_ctx_t;

/* The type-like node a bare name denotes for a reference made in `rel`: the
 * only type of that name declared in `rel` itself, else the only one in the
 * whole project, else the only one in the same .plcproj library as `rel`.
 * Candidates from another language never qualify (the same veto the generic
 * fallback applies). Anything else is ambiguous — no proximity or
 * insertion-order tie-break. */
static const cbm_gbuf_node_t *resolve_bare_type(const st_resolve_ctx_t *rc, const char *rel,
                                                const char *name) {
    const char **qns = NULL;
    int n = 0;
    cbm_registry_find_by_name(rc->reg, name, &qns, &n);
    const cbm_gbuf_node_t *in_file = NULL;
    const cbm_gbuf_node_t *any = NULL;
    const cbm_gbuf_node_t *same_lib = NULL;
    int in_file_hits = 0;
    int any_hits = 0;
    int same_lib_hits = 0;
    for (int i = 0; i < n; i++) {
        const cbm_gbuf_node_t *node = cbm_gbuf_find_by_qn(rc->gbuf, qns[i]);
        if (!node || !cbm_label_is_type_like(node->label) ||
            cbm_suppress_cross_language_ref(rc->lang, node->file_path)) {
            continue;
        }
        any = node;
        any_hits++;
        if (node->file_path && strcmp(node->file_path, rel) == 0) {
            in_file = node;
            in_file_hits++;
        }
        if (rc->ns && cbm_tc_ns_same_library(rc->ns, rel, node->file_path)) {
            same_lib = node;
            same_lib_hits++;
        }
    }
    if (in_file_hits == 1) {
        return in_file;
    }
    if (any_hits == 1) {
        return any;
    }
    return same_lib_hits == 1 ? same_lib : NULL;
}

/* The type-like node a type name denotes, or NULL. A qualified name goes
 * through the .plcproj namespace alias (TwinCAT only), exactly as a qualified
 * base class does. */
static const cbm_gbuf_node_t *resolve_type(const st_resolve_ctx_t *rc, const char *rel,
                                           const char *name) {
    if (!is_plain_type_name(name)) {
        return NULL;
    }
    if (!strchr(name, '.')) {
        return resolve_bare_type(rc, rel, name);
    }
    if (!cbm_tc_ns_applies(rc->lang, name)) {
        return NULL;
    }
    const char *qn = cbm_tc_ns_resolve_base(rc->ns, rc->reg, rc->gbuf, rel, name);
    const cbm_gbuf_node_t *node = qn ? cbm_gbuf_find_by_qn(rc->gbuf, qn) : NULL;
    return node && cbm_label_is_type_like(node->label) ? node : NULL;
}

/* The Field named `member` under `owner`, or NULL. Exact spelling: the graph
 * keys members by qualified name. */
static const cbm_gbuf_node_t *field_of(const cbm_gbuf_t *gbuf, const cbm_gbuf_node_t *owner,
                                       const char *member) {
    char qn[CBM_SZ_1K];
    int w = snprintf(qn, sizeof(qn), "%s.%s", owner->qualified_name, member);
    if (w <= 0 || (size_t)w >= sizeof(qn)) {
        return NULL;
    }
    const cbm_gbuf_node_t *f = cbm_gbuf_find_by_qn(gbuf, qn);
    return f && f->label && strcmp(f->label, "Field") == 0 ? f : NULL;
}

const cbm_gbuf_node_t *cbm_st_resolve_plain(const cbm_registry_t *reg, const cbm_gbuf_t *gbuf,
                                            CBMLanguage lang, const char *module_qn,
                                            const char **imp_keys, const char **imp_vals,
                                            int imp_count, const CBMUsage *usage) {
    if (!reg || !gbuf || !usage || !usage->ref_name) {
        return NULL;
    }
    /* Mirror of the generic textual fallback in pass_usages.c /
     * pass_parallel.c, minus the LSP branch ST never has. Keep in sync. */
    cbm_resolution_t res =
        cbm_registry_resolve(reg, usage->ref_name, module_qn, imp_keys, imp_vals, imp_count);
    if (!res.qualified_name || res.qualified_name[0] == '\0') {
        return NULL;
    }
    if (!cbm_pipeline_reference_candidate_fallback_allowed(lang, usage, res.strategy, imp_keys,
                                                           imp_count)) {
        return NULL;
    }
    const cbm_gbuf_node_t *tgt = cbm_gbuf_find_by_qn(gbuf, res.qualified_name);
    if (!tgt || cbm_suppress_cross_language_ref(lang, tgt->file_path)) {
        return NULL;
    }
    if (usage->semantic_reference_blocked &&
        (usage->semantic_reference_local_shadow || cbm_pipeline_node_is_callable_target(tgt))) {
        return NULL;
    }
    /* Belt and braces: DUT members are not registered, so this never fires. */
    return cbm_st_is_dut_member(gbuf, tgt) ? NULL : tgt;
}

const cbm_gbuf_node_t *cbm_st_resolve_member(cbm_tc_ns_t *ns, const cbm_registry_t *reg,
                                             const cbm_gbuf_t *gbuf, const char *rel,
                                             CBMLanguage lang, const CBMUsage *usage) {
    if (!reg || !gbuf || !rel || !usage || !usage->ref_name || !usage->member_qualifier ||
        !usage->member_qualifier[0]) {
        return NULL;
    }
    st_resolve_ctx_t rc = {ns, reg, gbuf, lang};

    /* Split the canonical dotted receiver into segments. */
    char buf[CBM_SZ_1K];
    if (snprintf(buf, sizeof(buf), "%s", usage->member_qualifier) >= (int)sizeof(buf)) {
        return NULL;
    }
    const char *seg[ST_MAX_SEGMENTS];
    int nseg = 0;
    for (char *p = buf; p && nseg < ST_MAX_SEGMENTS;) {
        char *dot = strchr(p, '.');
        if (dot) {
            *dot = '\0';
        }
        if (!p[0]) {
            return NULL;
        }
        seg[nseg++] = p;
        p = dot ? dot + 1 : NULL;
    }
    if (nseg == 0 || nseg == ST_MAX_SEGMENTS) {
        return NULL;
    }

    const cbm_gbuf_node_t *cur = NULL;
    int next = 0;
    if (usage->qualifier_type) {
        /* `_par.Inner.Depth` with VAR _par : T_Par — the head is a variable. */
        cur = resolve_type(&rc, rel, usage->qualifier_type);
        next = 1;
    } else {
        /* The head is a type path: `Vnd_Core.E_AlarmState` (alias + type) or `E_State`. */
        if (nseg >= 2) {
            char two[CBM_SZ_512];
            snprintf(two, sizeof(two), "%s.%s", seg[0], seg[1]);
            cur = resolve_type(&rc, rel, two);
            next = 2;
        }
        if (!cur) {
            cur = resolve_type(&rc, rel, seg[0]);
            next = 1;
        }
    }
    for (int i = next; cur && i < nseg; i++) {
        const cbm_gbuf_node_t *f = field_of(gbuf, cur, seg[i]);
        char declared[CBM_SZ_512];
        /* The field's declared type means what it means in the FIELD's file. */
        cur = f && f->file_path &&
                      json_string_prop(f->properties_json, "return_type", declared,
                                       sizeof(declared))
                  ? resolve_type(&rc, f->file_path, declared)
                  : NULL;
    }
    return cur ? field_of(gbuf, cur, usage->ref_name) : NULL;
}

/* ── Occurrence aggregation ─────────────────────────────────────────────── */

typedef struct {
    int64_t src;
    int64_t tgt;
    char *callee; /* owned */
    uint32_t line;
    int count;
} st_occ_t;

struct cbm_st_usage_agg {
    CBMHashTable *by_pair; /* "src:tgt" (owned key) -> st_occ_t* (owned) */
    st_occ_t **items;
    int count;
    int cap;
};

cbm_st_usage_agg_t *cbm_st_usage_agg_new(void) {
    cbm_st_usage_agg_t *agg = calloc(1, sizeof(*agg));
    if (!agg) {
        return NULL;
    }
    agg->by_pair = cbm_ht_create(0);
    if (!agg->by_pair) {
        free(agg);
        return NULL;
    }
    return agg;
}

static void agg_add(cbm_st_usage_agg_t *agg, int64_t src, int64_t tgt, const char *callee,
                    uint32_t line) {
    if (!agg || src == tgt) {
        return;
    }
    char key[CBM_SZ_64];
    snprintf(key, sizeof(key), "%lld:%lld", (long long)src, (long long)tgt);
    st_occ_t *occ = cbm_ht_get(agg->by_pair, key);
    if (occ) {
        occ->count++;
        if (line > 0 && (occ->line == 0 || line < occ->line)) {
            occ->line = line;
        }
        return;
    }
    if (agg->count == agg->cap) {
        int ncap = agg->cap ? agg->cap * 2 : 64;
        st_occ_t **grown = realloc(agg->items, (size_t)ncap * sizeof(*grown));
        if (!grown) {
            return;
        }
        agg->items = grown;
        agg->cap = ncap;
    }
    occ = calloc(1, sizeof(*occ));
    char *key_copy = strdup(key);
    if (!occ || !key_copy) {
        free(occ);
        free(key_copy);
        return;
    }
    occ->src = src;
    occ->tgt = tgt;
    occ->callee = callee ? strdup(callee) : NULL;
    occ->line = line;
    occ->count = 1;
    agg->items[agg->count++] = occ;
    cbm_ht_set(agg->by_pair, key_copy, occ);
}

void cbm_st_usage_agg_add(cbm_st_usage_agg_t *agg, const cbm_gbuf_node_t *src,
                          const cbm_gbuf_node_t *tgt, const cbm_gbuf_node_t *member,
                          const CBMUsage *usage) {
    if (!agg || !src || !usage) {
        return;
    }
    if (tgt) {
        agg_add(agg, src->id, tgt->id, usage->ref_name, usage->start_line);
    }
    if (member && member != tgt) {
        /* The member edge names the full token so a reader sees which enum it is. */
        char callee[CBM_SZ_512];
        snprintf(callee, sizeof(callee), "%s.%s",
                 usage->member_qualifier ? usage->member_qualifier : "", usage->ref_name);
        agg_add(agg, src->id, member->id, callee, usage->start_line);
    }
}

static void free_key(const char *key, void *value, void *userdata) {
    (void)value;
    (void)userdata;
    free((void *)key);
}

int cbm_st_usage_agg_flush(cbm_st_usage_agg_t *agg, cbm_gbuf_t *gbuf) {
    if (!agg) {
        return 0;
    }
    int edges = 0;
    for (int i = 0; i < agg->count; i++) {
        st_occ_t *occ = agg->items[i];
        /* ref_name is sliced source text: escape it or the JSON is malformed
         * (same rule and sizes as the generic USAGE emit). */
        char esc[CBM_SZ_256];
        cbm_json_escape(esc, sizeof(esc), occ->callee ? occ->callee : "");
        char props[CBM_SZ_512];
        snprintf(props, sizeof(props), "{\"callee\":\"%s\",\"line\":%u,\"count\":%d}", esc,
                 occ->line, occ->count);
        if (gbuf && cbm_gbuf_insert_edge(gbuf, occ->src, occ->tgt, "USAGE", props) > 0) {
            edges++;
        }
        free(occ->callee);
        free(occ);
    }
    free(agg->items);
    cbm_ht_foreach(agg->by_pair, free_key, NULL);
    cbm_ht_free(agg->by_pair);
    free(agg);
    return edges;
}
