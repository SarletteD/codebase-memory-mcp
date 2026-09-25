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
 * cbm_st_resolve_member + the aggregator, so they cannot diverge. A usage
 * whose member resolves exactly contributes only the member edge.
 */
#include "foundation/constants.h"
#include "foundation/hash_table.h"
#include "foundation/mem_core.h" // aggregator is per-pass scratch, like pass_lsp_cross.c's
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

/* The type-like node the receiver chain `qualifier` denotes: its head through
 * `qualifier_type` (a declared variable) or as a type path, every further
 * segment through the Field's declared return_type. NULL when any hop fails. */
static const cbm_gbuf_node_t *receiver_type(const st_resolve_ctx_t *rc, const char *rel,
                                            const char *qualifier, const char *qualifier_type) {
    char buf[CBM_SZ_1K];
    if (snprintf(buf, sizeof(buf), "%s", qualifier) >= (int)sizeof(buf)) {
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
    if (qualifier_type) {
        cur = resolve_type(rc, rel, qualifier_type);
        next = 1;
    } else {
        if (nseg >= 2) {
            char two[CBM_SZ_512];
            snprintf(two, sizeof(two), "%s.%s", seg[0], seg[1]);
            cur = resolve_type(rc, rel, two);
            next = 2;
        }
        if (!cur) {
            cur = resolve_type(rc, rel, seg[0]);
            next = 1;
        }
    }
    for (int i = next; cur && i < nseg; i++) {
        const cbm_gbuf_node_t *f = field_of(rc->gbuf, cur, seg[i]);
        char declared[CBM_SZ_512];
        /* The field's declared type means what it means in the FIELD's file. */
        cur =
            f && f->file_path &&
                    json_string_prop(f->properties_json, "return_type", declared, sizeof(declared))
                ? resolve_type(rc, f->file_path, declared)
                : NULL;
    }
    return cur;
}

const cbm_gbuf_node_t *cbm_st_resolve_member(cbm_tc_ns_t *ns, const cbm_registry_t *reg,
                                             const cbm_gbuf_t *gbuf, const char *rel,
                                             CBMLanguage lang, const CBMUsage *usage) {
    if (!reg || !gbuf || !rel || !usage || !usage->ref_name || !usage->member_qualifier ||
        !usage->member_qualifier[0]) {
        return NULL;
    }
    st_resolve_ctx_t rc = {ns, reg, gbuf, lang};
    const cbm_gbuf_node_t *owner =
        receiver_type(&rc, rel, usage->member_qualifier, usage->qualifier_type);
    return owner ? field_of(gbuf, owner, usage->ref_name) : NULL;
}

/* Bases queued per lookup, per side; deeper hierarchies are not real ST code.
 * A base dropped at this cap makes the walk incomplete, so a miss falls back
 * to the generic resolver instead of claiming the method does not exist. */
#define ST_MAX_BASES 32

/* Next base name in a JSON string array starting at *p ("[\"A\",\"B\"]"),
 * copied into out; false at the end. Names never carry escapes. */
static bool next_base(const char **p, char *out, size_t out_size) {
    const char *q = strchr(*p, '"');
    if (!q) {
        return false;
    }
    const char *e = strchr(q + 1, '"');
    if (!e || (size_t)(e - q - 1) >= out_size) {
        return false;
    }
    memcpy(out, q + 1, (size_t)(e - q - 1));
    out[e - q - 1] = '\0';
    *p = e + 1;
    return true;
}

/* The types one method lookup visits. base_classes mixes EXTENDS and
 * IMPLEMENTS names, so they are split: the owner's EXTENDS chain is searched
 * before any interface, and a concrete receiver binds the implementation
 * rather than the contract that merely declares the method. */
typedef struct {
    const cbm_gbuf_node_t *chain[ST_MAX_BASES]; /* owner + non-Interface bases */
    const cbm_gbuf_node_t *itf[ST_MAX_BASES];   /* Interface bases + their bases */
    int nchain;
    int nitf;
    bool complete; /* every base resolved and none was dropped at the cap */
} st_walk_t;

static bool walk_seen(const st_walk_t *w, const cbm_gbuf_node_t *n) {
    for (int i = 0; i < w->nchain; i++) {
        if (w->chain[i] == n) {
            return true;
        }
    }
    for (int i = 0; i < w->nitf; i++) {
        if (w->itf[i] == n) {
            return true;
        }
    }
    return false;
}

/* Queue the bases of `t`, each resolved in t's own file. Below an interface
 * everything stays on the interface side. */
static void walk_queue_bases(const st_resolve_ctx_t *rc, st_walk_t *w, const cbm_gbuf_node_t *t,
                             bool itf_side) {
    /* base_classes is written by append_json_str_array (pass_definitions.c
     * / pass_parallel.c build_def_props): plain `,"base_classes":["A","B"]`,
     * no escaping. Scanning it with strstr/strchr instead of a JSON parser
     * relies on that — a base name never carries a quote or bracket, which
     * holds for every ST identifier (is_plain_type_name's character set,
     * plus the dots a qualified base contributes). */
    const char *bases =
        t->properties_json ? strstr(t->properties_json, "\"base_classes\":[") : NULL;
    const char *end = bases ? strchr(bases, ']') : NULL;
    if (!bases || !end) {
        return;
    }
    const char *p = bases + strlen("\"base_classes\":[");
    char base[CBM_SZ_512];
    while (p < end) {
        if (!next_base(&p, base, sizeof(base))) {
            /* A quote still inside the list means a name too long for `base`. */
            const char *q = strchr(p, '"');
            if (q && q < end) {
                w->complete = false;
            }
            break;
        }
        const cbm_gbuf_node_t *b = t->file_path ? resolve_type(rc, t->file_path, base) : NULL;
        if (!b) {
            w->complete = false;
            continue;
        }
        if (walk_seen(w, b)) {
            continue;
        }
        bool is_itf = itf_side || (b->label && strcmp(b->label, "Interface") == 0);
        if (is_itf && w->nitf < ST_MAX_BASES) {
            w->itf[w->nitf++] = b;
        } else if (!is_itf && w->nchain < ST_MAX_BASES) {
            w->chain[w->nchain++] = b;
        } else {
            w->complete = false;
        }
    }
}

/* ASCII case-insensitive equality; ST identifiers are ASCII. */
static bool ci_equal(const char *a, const char *b) {
    for (; *a && *b; a++, b++) {
        char x = (*a >= 'a' && *a <= 'z') ? (char)(*a - 'a' + 'A') : *a;
        char y = (*b >= 'a' && *b <= 'z') ? (char)(*b - 'a' + 'A') : *b;
        if (x != y) {
            return false;
        }
    }
    return *a == *b;
}

/* The Method `name` declared directly on `t`, or NULL. ST identifiers are
 * case-insensitive, so a miss on the exact qualified name retries over t's
 * DEFINES_METHOD edges by name. */
static const cbm_gbuf_node_t *own_method(const cbm_gbuf_t *gbuf, const cbm_gbuf_node_t *t,
                                         const char *name) {
    char qn[CBM_SZ_1K];
    int w = snprintf(qn, sizeof(qn), "%s.%s", t->qualified_name, name);
    if (w > 0 && (size_t)w < sizeof(qn)) {
        const cbm_gbuf_node_t *m = cbm_gbuf_find_by_qn(gbuf, qn);
        if (m && m->label && strcmp(m->label, "Method") == 0) {
            return m;
        }
    }
    const cbm_gbuf_edge_t **edges = NULL;
    int count = 0;
    cbm_gbuf_find_edges_by_source_type(gbuf, t->id, "DEFINES_METHOD", &edges, &count);
    for (int i = 0; i < count; i++) {
        const cbm_gbuf_node_t *m = cbm_gbuf_find_by_id(gbuf, edges[i]->target_id);
        if (m && m->name && m->label && strcmp(m->label, "Method") == 0 &&
            ci_equal(m->name, name)) {
            return m;
        }
    }
    return NULL;
}

/* The Method `name` on `owner` or its bases: the EXTENDS chain breadth-first,
 * then the interfaces. An Interface owner is its own chain. *complete tells a
 * miss over the whole hierarchy apart from one that could not see all of it. */
static const cbm_gbuf_node_t *method_of_type(const st_resolve_ctx_t *rc,
                                             const cbm_gbuf_node_t *owner, const char *name,
                                             bool *complete) {
    st_walk_t w;
    w.nchain = 0;
    w.nitf = 0;
    w.complete = true;
    w.chain[w.nchain++] = owner;
    for (int i = 0; i < w.nchain; i++) {
        const cbm_gbuf_node_t *m = own_method(rc->gbuf, w.chain[i], name);
        if (m) {
            return m;
        }
        walk_queue_bases(rc, &w, w.chain[i], false);
    }
    for (int i = 0; i < w.nitf; i++) {
        const cbm_gbuf_node_t *m = own_method(rc->gbuf, w.itf[i], name);
        if (m) {
            return m;
        }
        walk_queue_bases(rc, &w, w.itf[i], true);
    }
    *complete = w.complete;
    return NULL;
}

cbm_st_call_status_t cbm_st_resolve_call(cbm_tc_ns_t *ns, const cbm_registry_t *reg,
                                         const cbm_gbuf_t *gbuf, const char *rel, CBMLanguage lang,
                                         const CBMCall *call, const cbm_gbuf_node_t **out_method) {
    *out_method = NULL;
    if (!reg || !gbuf || !rel || !call || !call->callee_name || !call->qualifier_type ||
        !call->member_qualifier || !call->member_qualifier[0]) {
        return CBM_ST_CALL_UNTYPED;
    }
    const char *leaf = strrchr(call->callee_name, '.');
    leaf = leaf ? leaf + 1 : call->callee_name;
    if (!leaf[0]) {
        return CBM_ST_CALL_UNTYPED;
    }
    st_resolve_ctx_t rc = {ns, reg, gbuf, lang};
    const cbm_gbuf_node_t *owner =
        receiver_type(&rc, rel, call->member_qualifier, call->qualifier_type);
    if (!owner) {
        return CBM_ST_CALL_UNTYPED;
    }
    bool complete = true;
    *out_method = method_of_type(&rc, owner, leaf, &complete);
    if (*out_method) {
        return CBM_ST_CALL_FOUND;
    }
    return complete ? CBM_ST_CALL_NOT_FOUND : CBM_ST_CALL_UNTYPED;
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
    cbm_st_usage_agg_t *agg = cbm_calloc(CBM_MEM_CLASS_OTHER, sizeof(*agg));
    if (!agg) {
        return NULL;
    }
    agg->by_pair = cbm_ht_create(0);
    if (!agg->by_pair) {
        cbm_free(CBM_MEM_CLASS_OTHER, agg);
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
        st_occ_t **grown =
            cbm_realloc(CBM_MEM_CLASS_OTHER, agg->items, (size_t)ncap * sizeof(*grown));
        if (!grown) {
            return;
        }
        agg->items = grown;
        agg->cap = ncap;
    }
    occ = cbm_calloc(CBM_MEM_CLASS_OTHER, sizeof(*occ));
    char *key_copy = cbm_mem_strdup(CBM_MEM_CLASS_OTHER, key);
    if (!occ || !key_copy) {
        cbm_free(CBM_MEM_CLASS_OTHER, occ);
        cbm_free(CBM_MEM_CLASS_OTHER, key_copy);
        return;
    }
    occ->src = src;
    occ->tgt = tgt;
    occ->callee = callee ? cbm_mem_strdup(CBM_MEM_CLASS_OTHER, callee) : NULL;
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
    /* An exact member hit is authoritative and always contributes its edge,
     * including when the bare-name registry guess landed on the same node
     * (the common case: a property/field whose name is unique in the
     * project). The bare-name edge is only useful as a fallback when the
     * member did not resolve — otherwise it would be redundant at best and
     * wrong at worst (another FB's property of the same name). */
    if (tgt && !member) {
        agg_add(agg, src->id, tgt->id, usage->ref_name, usage->start_line);
    }
    if (member) {
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
    cbm_free(CBM_MEM_CLASS_OTHER, (void *)key);
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
        cbm_free(CBM_MEM_CLASS_OTHER, occ->callee);
        cbm_free(CBM_MEM_CLASS_OTHER, occ);
    }
    cbm_free(CBM_MEM_CLASS_OTHER, agg->items);
    cbm_ht_foreach(agg->by_pair, free_key, NULL);
    cbm_ht_free(agg->by_pair);
    cbm_free(CBM_MEM_CLASS_OTHER, agg);
    return edges;
}
