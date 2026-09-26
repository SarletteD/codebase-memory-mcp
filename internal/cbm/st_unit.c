/*
 * st_unit.c — parser text and line map for one Structured Text source.
 *
 * Exports place a FUNCTION_BLOCK's METHOD/PROPERTY members after
 * END_FUNCTION_BLOCK. The grammar accepts them only inside the block, after
 * every VAR block and before the first body statement (a VAR block after a
 * member, or a member after a statement, is an ERROR), so a planning scan
 * finds, per container, the last declaration line and the member blocks that
 * trail its terminator; the emitter then writes the lines in the order the
 * grammar needs and records each line's original number.
 *
 * The scan tokenizes like the grammar: (* *) comments do not nest, strings
 * never span lines. It additionally skips // and slash-star comments and
 * {pragma} spans, so no keyword inside them is ever taken for structure.
 * Keywords match case-insensitively. Containers are FUNCTION_BLOCK and
 * INTERFACE only: the grammar's PROGRAM accepts no members (the dialect pass
 * already turns a PROGRAM that owns members into a FUNCTION_BLOCK) and it has
 * no ACTION at all, so an ACTION between trailing members stays in place.
 * Blocks move as whole lines; a block boundary that shares a line with other
 * code stops the reorder for that container instead of splitting the line.
 */
#include "st_unit.h"

#include "st_dialect.h"

#include "foundation/constants.h"
#include "foundation/mem_core.h" // per-file transient: freed inside one extraction call

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

enum {
    ST_UTF8_BYTE = 0x80,
    ST_GROW_MIN = 8,
    ST_GROW_FACTOR = 2,
    ST_FIRST_LINE = 1,
};

static const char END_PROPERTY_TAIL[] = " END_PROPERTY";

/* ── tokens ───────────────────────────────────────────────────────────────── */

typedef enum { TOK_EOF, TOK_WORD, TOK_CODE } StTokKind;

typedef struct {
    StTokKind kind;
    size_t start;
    size_t end;
    uint32_t line;
    bool first_on_line; /* no code token precedes it on its line */
} StTok;

typedef struct {
    const char *s;
    size_t n;
    size_t pos;
    uint32_t line;
    uint32_t last_code_line;
} StLex;

static bool is_word_start(char c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_';
}

static bool is_word_char(char c) {
    return is_word_start(c) || (c >= '0' && c <= '9') || (unsigned char)c >= ST_UTF8_BYTE;
}

static char up(char c) {
    if (c >= 'a' && c <= 'z') {
        return (char)(c - ('a' - 'A'));
    }
    return c;
}

/* Advance past `close`, counting the newlines crossed; runs to the end when
 * the span is unterminated. */
static void lex_skip_until(StLex *lx, const char *close) {
    size_t cl = strlen(close);
    while (lx->pos < lx->n) {
        if (lx->n - lx->pos >= cl && memcmp(lx->s + lx->pos, close, cl) == 0) {
            lx->pos += cl;
            return;
        }
        if (lx->s[lx->pos] == '\n') {
            lx->line++;
        }
        lx->pos++;
    }
}

/* Skip blanks, newlines, comments and pragmas; true when a token follows. */
static bool lex_skip_trivia(StLex *lx) {
    const char *s = lx->s;
    while (lx->pos < lx->n) {
        char c = s[lx->pos];
        char d = '\0';
        if (lx->pos + SKIP_ONE < lx->n) {
            d = s[lx->pos + SKIP_ONE];
        }
        if (c == '\n') {
            lx->line++;
            lx->pos++;
        } else if (c == ' ' || c == '\t' || c == '\r' || c == '\f' || c == '\v') {
            lx->pos++;
        } else if (c == '(' && d == '*') {
            lx->pos += PAIR_LEN;
            lex_skip_until(lx, "*)");
        } else if (c == '/' && d == '*') {
            lx->pos += PAIR_LEN;
            lex_skip_until(lx, "*/");
        } else if (c == '/' && d == '/') {
            while (lx->pos < lx->n && s[lx->pos] != '\n') {
                lx->pos++;
            }
        } else if (c == '{') {
            lx->pos++;
            lex_skip_until(lx, "}");
        } else {
            return true;
        }
    }
    return false;
}

/* Skip a '...' or "..." literal ($ escapes the next byte); stops at a
 * newline so a stray quote cannot swallow the rest of the file. */
static void lex_skip_string(StLex *lx) {
    char q = lx->s[lx->pos++];
    while (lx->pos < lx->n && lx->s[lx->pos] != '\n') {
        char c = lx->s[lx->pos];
        if (c == '$' && lx->pos + SKIP_ONE < lx->n && lx->s[lx->pos + SKIP_ONE] != '\n') {
            lx->pos += PAIR_LEN;
            continue;
        }
        lx->pos++;
        if (c == q) {
            return;
        }
    }
}

static StTok lex_next(StLex *lx) {
    StTok t = {TOK_EOF, lx->n, lx->n, lx->line, false};
    if (!lex_skip_trivia(lx)) {
        t.line = lx->line;
        return t;
    }
    t.start = lx->pos;
    t.line = lx->line;
    char c = lx->s[lx->pos];
    if (c == '\'' || c == '"') {
        lex_skip_string(lx);
        t.kind = TOK_CODE;
    } else if (is_word_start(c)) {
        while (lx->pos < lx->n && is_word_char(lx->s[lx->pos])) {
            lx->pos++;
        }
        t.kind = TOK_WORD;
    } else {
        lx->pos++;
        t.kind = TOK_CODE;
    }
    t.end = lx->pos;
    t.first_on_line = t.line != lx->last_code_line;
    lx->last_code_line = t.line;
    return t;
}

/* Whole-token, case-insensitive match against an UPPERCASE keyword. */
static bool tok_is(const StLex *lx, const StTok *t, const char *kw) {
    size_t kl = strlen(kw);
    if (t->kind != TOK_WORD || t->end - t->start != kl) {
        return false;
    }
    for (size_t k = 0; k < kl; k++) {
        if (up(lx->s[t->start + k]) != kw[k]) {
            return false;
        }
    }
    return true;
}

static bool tok_is_char(const StLex *lx, const StTok *t, char c) {
    return t->kind == TOK_CODE && t->end - t->start == SKIP_ONE && lx->s[t->start] == c;
}

static bool tok_in(const StLex *lx, const StTok *t, const char *const *kws) {
    for (size_t k = 0; kws[k]; k++) {
        if (tok_is(lx, t, kws[k])) {
            return true;
        }
    }
    return false;
}

/* Every section keyword a declaration block opens with (VAR_STAT and
 * VAR_INST are vendor sections the dialect pass maps to VAR). */
static bool tok_opens_var(const StLex *lx, const StTok *t) {
    static const char *const SECTIONS[] = {"VAR",        "VAR_INPUT",  "VAR_OUTPUT", "VAR_IN_OUT",
                                           "VAR_TEMP",   "VAR_STAT",   "VAR_INST",   "VAR_EXTERNAL",
                                           "VAR_GLOBAL", "VAR_CONFIG", "VAR_ACCESS", NULL};
    return tok_in(lx, t, SECTIONS);
}

static bool tok_is_member(const StLex *lx, const StTok *t) {
    return tok_is(lx, t, "METHOD") || tok_is(lx, t, "PROPERTY");
}

/* A keyword that cannot belong to a PROPERTY once its accessors are done. */
static bool tok_ends_property(const StLex *lx, const StTok *t) {
    static const char *const KWS[] = {
        "METHOD",  "PROPERTY",  "ACTION",        "FUNCTION", "FUNCTION_BLOCK", "END_FUNCTION_BLOCK",
        "PROGRAM", "INTERFACE", "END_INTERFACE", "TYPE",     "VAR_GLOBAL",     NULL};
    return tok_in(lx, t, KWS);
}

static StTok lex_peek(const StLex *lx) {
    StLex probe = *lx;
    return lex_next(&probe);
}

/* The header of the next POU: a POU keyword first on its line and followed
 * by a name (so an identifier spelled "Type" in a statement is not one). */
static bool tok_starts_pou(const StLex *lx, const StTok *t) {
    static const char *const POUS[] = {"FUNCTION_BLOCK", "FUNCTION", "PROGRAM",
                                       "INTERFACE",      "TYPE",     NULL};
    if (!t->first_on_line || !tok_in(lx, t, POUS)) {
        return false;
    }
    return lex_peek(lx).kind == TOK_WORD;
}

/* Consume tokens up to and including the word `kw`. False at the end of the
 * source, or before the header of the next POU (left unconsumed): a block
 * that lacks its terminator must not borrow the next block's. */
static bool lex_skip_to_word(StLex *lx, const char *kw, StTok *found) {
    for (;;) {
        StLex save = *lx;
        StTok t = lex_next(lx);
        if (t.kind == TOK_EOF) {
            return false;
        }
        if (tok_is(lx, &t, kw)) {
            *found = t;
            return true;
        }
        if (tok_starts_pou(lx, &t)) {
            *lx = save;
            return false;
        }
    }
}

/* True when nothing but an optional ';' follows on `line`: a block that ends
 * there can move as whole lines. Consumes that ';'. */
static bool lex_line_clear_after(StLex *lx, uint32_t line) {
    StLex save = *lx;
    StTok t = lex_next(lx);
    if (t.kind != TOK_EOF && t.line == line && tok_is_char(lx, &t, ';')) {
        save = *lx;
        t = lex_next(lx);
    }
    *lx = save;
    return t.kind == TOK_EOF || t.line > line;
}

/* ── plan ─────────────────────────────────────────────────────────────────── */

typedef struct {
    uint32_t first;
    uint32_t last;
} StLineRange;

/* Member line ranges [first_range, first_range + range_count) are emitted
 * right after original line `after`. */
typedef struct {
    uint32_t after;
    int first_range;
    int range_count;
} StHoist;

/* Byte offsets, ascending. */
typedef struct {
    size_t *at;
    int count;
    int cap;
} StOffsets;

typedef struct {
    StLineRange *ranges;
    int nranges;
    int cap_ranges;
    StHoist *hoists;
    int nhoists;
    int cap_hoists;
    StOffsets tails;  /* END_PROPERTY_TAIL is inserted before these bytes */
    StOffsets blanks; /* these ';' bytes become blanks */
    bool oom;
} StPlan;

/* Planned edits so far, to drop the ones of a member or block given up on. */
typedef struct {
    int tails;
    int blanks;
} StMark;

/* Room for one more element in a plan array; false (and oom) on failure. */
static bool plan_reserve(StPlan *pl, void **items, int *cap, int count, size_t elem) {
    if (pl->oom) {
        return false;
    }
    if (count < *cap) {
        return true;
    }
    int ncap = *cap ? *cap * ST_GROW_FACTOR : ST_GROW_MIN;
    void *np = cbm_realloc(CBM_MEM_CLASS_EXTRACT, *items, (size_t)ncap * elem);
    if (!np) {
        pl->oom = true;
        return false;
    }
    *items = np;
    *cap = ncap;
    return true;
}

static void plan_add_range(StPlan *pl, uint32_t first, uint32_t last) {
    if (plan_reserve(pl, (void **)&pl->ranges, &pl->cap_ranges, pl->nranges, sizeof(*pl->ranges))) {
        pl->ranges[pl->nranges++] = (StLineRange){first, last};
    }
}

static void plan_add_hoist(StPlan *pl, uint32_t after, int first_range, int count) {
    if (plan_reserve(pl, (void **)&pl->hoists, &pl->cap_hoists, pl->nhoists, sizeof(*pl->hoists))) {
        pl->hoists[pl->nhoists++] = (StHoist){after, first_range, count};
    }
}

static void plan_add_offset(StPlan *pl, StOffsets *o, size_t at) {
    if (o->count > 0 && o->at[o->count - SKIP_ONE] >= at) {
        return; /* already recorded (a rescanned member) */
    }
    if (plan_reserve(pl, (void **)&o->at, &o->cap, o->count, sizeof(*o->at))) {
        o->at[o->count++] = at;
    }
}

static StMark plan_mark(const StPlan *pl) {
    return (StMark){pl->tails.count, pl->blanks.count};
}

static void plan_rollback(StPlan *pl, StMark m) {
    pl->tails.count = m.tails;
    pl->blanks.count = m.blanks;
}

static void plan_free(StPlan *pl) {
    cbm_free(CBM_MEM_CLASS_EXTRACT, pl->ranges);
    cbm_free(CBM_MEM_CLASS_EXTRACT, pl->hoists);
    cbm_free(CBM_MEM_CLASS_EXTRACT, pl->tails.at);
    cbm_free(CBM_MEM_CLASS_EXTRACT, pl->blanks.at);
    memset(pl, 0, sizeof(*pl));
}

/* A ';' right after a member terminator is an empty statement to the
 * grammar: once the member sits in its block, that statement opens the body
 * and every later member becomes an error. Plan it as a blank. */
static void plan_blank_semicolon(StLex *lx, StPlan *pl, const StTok *terminator) {
    StTok t = lex_peek(lx);
    if (t.kind != TOK_EOF && t.line == terminator->line && tok_is_char(lx, &t, ';')) {
        plan_add_offset(pl, &pl->blanks, t.start);
    }
}

/* True when `t` opens a GET or SET accessor not seen yet: the sole code on
 * its line. Records the accessor as seen. */
static bool tok_opens_accessor(const StLex *lx, const StTok *t, bool *seen_get, bool *seen_set) {
    bool get = tok_is(lx, t, "GET");
    bool set = tok_is(lx, t, "SET");
    if (!(get && !*seen_get) && !(set && !*seen_set)) {
        return false;
    }
    StTok next = lex_peek(lx);
    if (!t->first_on_line || (next.kind != TOK_EOF && next.line <= t->line)) {
        return false;
    }
    *seen_get = *seen_get || get;
    *seen_set = *seen_set || set;
    return true;
}

/* Consume one PROPERTY. Exports omit END_PROPERTY: the property then ends
 * after its last END_GET/END_SET, before the next member or POU keyword, and
 * an END_PROPERTY is planned right after that accessor terminator. GET/SET
 * open an accessor only once each and only as the sole code on their line,
 * so a statement such as "Get := n;" after the accessors is never taken for
 * one. An accessor's own access modifier ("GET PUBLIC") is already gone: the
 * dialect pass drops it, as the grammar has no place for it either. */
static bool skip_property(StLex *lx, StPlan *pl, uint32_t *end_line) {
    bool in_accessor = false;
    bool seen_get = false;
    bool seen_set = false;
    StTok accessor_end = {TOK_EOF, 0, 0, 0, false};
    for (;;) {
        StLex save = *lx;
        StTok t = lex_next(lx);
        if (t.kind == TOK_EOF) {
            break;
        }
        if (in_accessor) {
            if (tok_is(lx, &t, "END_GET") || tok_is(lx, &t, "END_SET")) {
                in_accessor = false;
                accessor_end = t;
                plan_blank_semicolon(lx, pl, &t);
            }
            continue;
        }
        if (tok_is(lx, &t, "END_PROPERTY")) {
            plan_blank_semicolon(lx, pl, &t);
            *end_line = t.line;
            return true;
        }
        if (tok_opens_accessor(lx, &t, &seen_get, &seen_set)) {
            in_accessor = true;
            continue;
        }
        if (tok_ends_property(lx, &t) || tok_starts_pou(lx, &t)) {
            *lx = save;
            break;
        }
    }
    if (in_accessor || accessor_end.kind == TOK_EOF) {
        return false;
    }
    plan_add_offset(pl, &pl->tails, accessor_end.end);
    *end_line = accessor_end.line;
    return true;
}

/* Consume one METHOD or PROPERTY whose keyword is `head`; on failure every
 * edit planned for it is dropped. */
static bool skip_member(StLex *lx, StPlan *pl, const StTok *head, uint32_t *end_line) {
    StMark mark = plan_mark(pl);
    bool ok;
    if (tok_is(lx, head, "METHOD")) {
        StTok e;
        ok = lex_skip_to_word(lx, "END_METHOD", &e);
        if (ok) {
            plan_blank_semicolon(lx, pl, &e);
            *end_line = e.line;
        }
    } else {
        ok = skip_property(lx, pl, end_line);
    }
    if (!ok) {
        plan_rollback(pl, mark);
    }
    return ok;
}

/* Consume the declaration part of a container: header (name, EXTENDS and
 * IMPLEMENTS lists), VAR blocks and members already inside it. Stops before
 * the first body statement or the terminator; returns the last line holding
 * declaration code, or 0 when the declarations do not end. */
static uint32_t scan_declarations(StLex *lx, StPlan *pl, uint32_t header_line) {
    uint32_t last_decl = header_line;
    bool in_header = true;
    bool expect_name = true;
    for (;;) {
        StLex save = *lx;
        StTok t = lex_next(lx);
        if (t.kind == TOK_EOF) {
            return 0;
        }
        if (in_header) {
            if (expect_name && t.kind == TOK_WORD) {
                expect_name = false;
                last_decl = t.line;
                continue;
            }
            if (!expect_name && (tok_is(lx, &t, "EXTENDS") || tok_is(lx, &t, "IMPLEMENTS") ||
                                 tok_is_char(lx, &t, ',') || tok_is_char(lx, &t, '.'))) {
                expect_name = true;
                last_decl = t.line;
                continue;
            }
            in_header = false;
        }
        if (tok_opens_var(lx, &t)) {
            StTok e;
            if (!lex_skip_to_word(lx, "END_VAR", &e)) {
                return 0;
            }
            last_decl = e.line;
            continue;
        }
        if (tok_is_member(lx, &t)) {
            uint32_t end_line = 0;
            if (!skip_member(lx, pl, &t, &end_line)) {
                return 0;
            }
            last_decl = end_line;
            continue;
        }
        *lx = save;
        return last_decl;
    }
}

/* Collect the member blocks that follow a container's terminator line. A
 * member takes the comment lines above it along (its doc comment); an ACTION
 * is stepped over and stays where it is. Returns the ranges added. */
static int collect_trailing_members(StLex *lx, StPlan *pl, uint32_t end_line) {
    uint32_t prev_end = end_line;
    int added = 0;
    for (;;) {
        StLex save = *lx;
        StMark mark = plan_mark(pl);
        StTok t = lex_next(lx);
        if (t.kind != TOK_WORD || !t.first_on_line) {
            *lx = save;
            return added;
        }
        uint32_t block_end = 0;
        bool member = tok_is_member(lx, &t);
        bool ok = false;
        if (member) {
            ok = skip_member(lx, pl, &t, &block_end);
        } else if (tok_is(lx, &t, "ACTION")) {
            StTok e;
            ok = lex_skip_to_word(lx, "END_ACTION", &e);
            if (ok) {
                block_end = e.line;
            }
        }
        if (!ok || !lex_line_clear_after(lx, block_end)) {
            *lx = save;
            plan_rollback(pl, mark);
            return added;
        }
        if (member) {
            plan_add_range(pl, prev_end + SKIP_ONE, block_end);
            added++;
        }
        prev_end = block_end;
    }
}

/* Plan one FUNCTION_BLOCK / INTERFACE whose keyword was just consumed. A
 * block given up on moves nothing, but keeps the edits of its complete
 * members: exports often end an INTERFACE without END_INTERFACE, and its
 * properties still need their END_PROPERTY to reach the graph. */
static void plan_container(StLex *lx, StPlan *pl, uint32_t header_line, const char *end_kw) {
    uint32_t last_decl = scan_declarations(lx, pl, header_line);
    StTok end_tok;
    if (last_decl == 0 || !lex_skip_to_word(lx, end_kw, &end_tok) ||
        !lex_line_clear_after(lx, end_tok.line) || last_decl >= end_tok.line) {
        return;
    }
    int added = collect_trailing_members(lx, pl, end_tok.line);
    if (added > 0 && !pl->oom) {
        plan_add_hoist(pl, last_decl, pl->nranges - added, added);
    }
}

static void plan_source(const char *s, size_t n, StPlan *pl) {
    StLex lx = {s, n, 0, ST_FIRST_LINE, 0};
    for (;;) {
        StTok t = lex_next(&lx);
        if (t.kind == TOK_EOF || pl->oom) {
            return;
        }
        if (tok_is(&lx, &t, "FUNCTION_BLOCK")) {
            plan_container(&lx, pl, t.line, "END_FUNCTION_BLOCK");
        } else if (tok_is(&lx, &t, "INTERFACE")) {
            plan_container(&lx, pl, t.line, "END_INTERFACE");
        }
    }
}

/* ── emission ─────────────────────────────────────────────────────────────── */

typedef struct {
    const char *s;
    size_t n;
    const size_t *line_start; /* line_start[i] = offset of 1-based line i + 1; [lines] = n */
    uint32_t lines;
    const StPlan *pl;
    char *out;
    size_t len;
    uint32_t *map;
    uint32_t mapped;
} StEmit;

/* First offset >= at. */
static int offsets_lower_bound(const StOffsets *o, size_t at) {
    int lo = 0;
    int hi = o->count;
    while (lo < hi) {
        int mid = lo + ((hi - lo) / PAIR_LEN);
        if (o->at[mid] < at) {
            lo = mid + SKIP_ONE;
        } else {
            hi = mid;
        }
    }
    return lo;
}

static void emit_bytes(StEmit *em, const char *p, size_t n) {
    memcpy(em->out + em->len, p, n);
    em->len += n;
}

/* Append original line `line` with its planned tails and blanks. A moved
 * last line without a newline gets one, so the next line starts cleanly. */
static void emit_line(StEmit *em, uint32_t line, bool moved) {
    const StOffsets *tails = &em->pl->tails;
    const StOffsets *blanks = &em->pl->blanks;
    size_t from = em->line_start[line - SKIP_ONE];
    size_t to = em->line_start[line];
    int k = offsets_lower_bound(tails, from);
    int b = offsets_lower_bound(blanks, from);
    size_t pos = from;
    for (;;) {
        size_t next = to;
        if (k < tails->count && tails->at[k] < next) {
            next = tails->at[k];
        }
        if (b < blanks->count && blanks->at[b] < next) {
            next = blanks->at[b];
        }
        emit_bytes(em, em->s + pos, next - pos);
        pos = next;
        /* a tail may sit at the very end of a last line without newline */
        if (k < tails->count && tails->at[k] == pos && (pos < to || to == em->n)) {
            emit_bytes(em, END_PROPERTY_TAIL, sizeof(END_PROPERTY_TAIL) - SKIP_ONE);
            k++;
            continue;
        }
        if (b < blanks->count && blanks->at[b] == pos && pos < to) {
            em->out[em->len++] = ' ';
            pos++;
            b++;
            continue;
        }
        break;
    }
    if (moved && (to == from || em->s[to - SKIP_ONE] != '\n')) {
        em->out[em->len++] = '\n';
    }
    em->map[em->mapped++] = line;
}

static bool emit_all(StEmit *em, const bool *moved) {
    int h = 0;
    bool phantom = false;
    for (uint32_t line = ST_FIRST_LINE; line <= em->lines; line++) {
        if (moved[line]) {
            continue;
        }
        emit_line(em, line, false);
        for (; h < em->pl->nhoists && em->pl->hoists[h].after == line; h++) {
            const StHoist *ho = &em->pl->hoists[h];
            for (int r = ho->first_range; r < ho->first_range + ho->range_count; r++) {
                for (uint32_t m = em->pl->ranges[r].first; m <= em->pl->ranges[r].last; m++) {
                    phantom = phantom || m == em->lines;
                    emit_line(em, m, true);
                }
            }
        }
    }
    if (h != em->pl->nhoists || em->mapped != em->lines) {
        return false;
    }
    if (phantom) {
        /* The original last line had no newline and moved: the text now ends
         * in one, which opens an empty parser line after the last. */
        em->map[em->mapped++] = em->lines;
    }
    em->out[em->len] = '\0';
    return true;
}

/* Mark every planned member line; false when a plan entry is out of range or
 * two entries claim one line (the plan would duplicate a line). */
static bool mark_moved(const StPlan *pl, uint32_t lines, bool *moved) {
    for (int r = 0; r < pl->nranges; r++) {
        const StLineRange *rg = &pl->ranges[r];
        if (rg->first == 0 || rg->first > rg->last || rg->last > lines) {
            return false;
        }
        for (uint32_t m = rg->first; m <= rg->last; m++) {
            if (moved[m]) {
                return false;
            }
            moved[m] = true;
        }
    }
    for (int h = 0; h < pl->nhoists; h++) {
        if (moved[pl->hoists[h].after]) {
            return false;
        }
    }
    return true;
}

/* Write the planned parser text of s[0, n) into *out, replacing out->text.
 * False (out untouched) on any allocation failure or inconsistent plan. */
static bool unit_emit(const char *s, size_t n, const StPlan *pl, CBMStUnit *out) {
    uint32_t lines = ST_FIRST_LINE;
    for (size_t i = 0; i < n; i++) {
        lines += s[i] == '\n';
    }
    size_t *line_start =
        cbm_alloc(CBM_MEM_CLASS_EXTRACT, ((size_t)lines + SKIP_ONE) * sizeof(size_t));
    bool *moved = cbm_calloc(CBM_MEM_CLASS_EXTRACT, ((size_t)lines + SKIP_ONE) * sizeof(bool));
    /* the tails, plus a newline a moved last line may gain, plus the NUL */
    size_t cap = n + ((size_t)pl->tails.count * (sizeof(END_PROPERTY_TAIL) - SKIP_ONE)) + PAIR_LEN;
    char *text = cbm_alloc(CBM_MEM_CLASS_EXTRACT, cap);
    uint32_t *map = cbm_alloc(CBM_MEM_CLASS_EXTRACT, ((size_t)lines + SKIP_ONE) * sizeof(uint32_t));
    bool ok = line_start && moved && text && map && mark_moved(pl, lines, moved);
    if (ok) {
        uint32_t li = 0;
        line_start[li++] = 0;
        for (size_t i = 0; i < n; i++) {
            if (s[i] == '\n') {
                line_start[li++] = i + SKIP_ONE;
            }
        }
        line_start[lines] = n;
        StEmit em = {s, n, line_start, lines, pl, text, 0, map, 0};
        ok = emit_all(&em, moved);
        if (ok) {
            cbm_free(CBM_MEM_CLASS_EXTRACT, out->text);
            out->text = text;
            out->len = (int)em.len;
            text = NULL;
            if (pl->nhoists > 0) {
                out->src_line = map;
                out->lines = em.mapped;
                map = NULL;
            }
        }
    }
    cbm_free(CBM_MEM_CLASS_EXTRACT, line_start);
    cbm_free(CBM_MEM_CLASS_EXTRACT, moved);
    cbm_free(CBM_MEM_CLASS_EXTRACT, text);
    cbm_free(CBM_MEM_CLASS_EXTRACT, map);
    return ok;
}

/* ── range mapping ────────────────────────────────────────────────────────── */

/* Sort ranges by start and merge the ones that overlap or touch; returns the
 * new count. */
static int ranges_compact(uint32_t *starts, uint32_t *ends, int n) {
    for (int i = SKIP_ONE; i < n; i++) {
        uint32_t s = starts[i];
        uint32_t e = ends[i];
        int j = i;
        while (j > 0 && starts[j - SKIP_ONE] > s) {
            starts[j] = starts[j - SKIP_ONE];
            ends[j] = ends[j - SKIP_ONE];
            j--;
        }
        starts[j] = s;
        ends[j] = e;
    }
    int m = 0;
    for (int i = 0; i < n; i++) {
        if (m > 0 && starts[i] <= ends[m - SKIP_ONE] + SKIP_ONE) {
            ends[m - SKIP_ONE] = ends[i] > ends[m - SKIP_ONE] ? ends[i] : ends[m - SKIP_ONE];
            continue;
        }
        starts[m] = starts[i];
        ends[m] = ends[i];
        m++;
    }
    return m;
}

/* Append one original-line run, compacting when full; a run that still does
 * not fit is counted in *dropped. */
static void ranges_push(uint32_t *starts, uint32_t *ends, int *count, int cap, uint32_t s,
                        uint32_t e, int *dropped) {
    if (*count >= cap) {
        *count = ranges_compact(starts, ends, *count);
    }
    if (*count >= cap) {
        (*dropped)++;
        return;
    }
    starts[*count] = s;
    ends[*count] = e;
    (*count)++;
}

/* ── public API ───────────────────────────────────────────────────────────── */

bool cbm_st_unit_build(const char *src, int len, CBMStUnit *out) {
    memset(out, 0, sizeof(*out));
    int norm_len = 0;
    char *norm = cbm_st_normalize(src, len, &norm_len);
    if (!norm) {
        return false;
    }
    out->text = norm;
    out->len = norm_len;
    StPlan pl = {0};
    plan_source(norm, (size_t)norm_len, &pl);
    if (!pl.oom && (pl.nhoists > 0 || pl.tails.count > 0 || pl.blanks.count > 0)) {
        (void)unit_emit(norm, (size_t)norm_len, &pl, out); /* failure keeps the normalized text */
    }
    plan_free(&pl);
    return true;
}

uint32_t cbm_st_unit_line(const CBMStUnit *u, uint32_t parser_line) {
    if (!u || !u->src_line || parser_line == 0 || u->lines == 0) {
        return parser_line;
    }
    return u->src_line[(parser_line <= u->lines ? parser_line : u->lines) - SKIP_ONE];
}

int cbm_st_unit_map_ranges(const CBMStUnit *u, const uint32_t *starts, const uint32_t *ends, int n,
                           uint32_t *out_starts, uint32_t *out_ends, int cap, int *dropped) {
    int count = 0;
    if (cap <= 0) {
        *dropped += n;
        return 0;
    }
    for (int i = 0; i < n; i++) {
        if (starts[i] == 0 || starts[i] > ends[i]) {
            continue;
        }
        uint32_t run_start = cbm_st_unit_line(u, starts[i]);
        uint32_t run_end = run_start;
        for (uint32_t k = starts[i] + SKIP_ONE; k <= ends[i]; k++) {
            uint32_t o = cbm_st_unit_line(u, k);
            if (o == run_end + SKIP_ONE) {
                run_end = o;
                continue;
            }
            ranges_push(out_starts, out_ends, &count, cap, run_start, run_end, dropped);
            run_start = o;
            run_end = o;
        }
        ranges_push(out_starts, out_ends, &count, cap, run_start, run_end, dropped);
    }
    return ranges_compact(out_starts, out_ends, count);
}

void cbm_st_unit_free(CBMStUnit *u) {
    if (!u) {
        return;
    }
    cbm_free(CBM_MEM_CLASS_EXTRACT, u->text);
    cbm_free(CBM_MEM_CLASS_EXTRACT, u->src_line);
    memset(u, 0, sizeof(*u));
}
