/*
 * twincat_xml.c — TwinCAT PLC object XML -> IEC 61131-3 Structured Text.
 *
 * Two stages, both specified and measured before this port (Stage 1 viability
 * run over 1380 real files; the Python reference is the measurement tool):
 *
 *  1. Assembly, per FILE. Per-CDATA parsing errors on 100 % of blocks and
 *     per-object reassembly on 92.1 %, because METHOD and PROPERTY are only
 *     valid nested inside their FUNCTION_BLOCK and must precede its body
 *     statements. Order: declaration, methods, properties (all GETs, then all
 *     SETs), body, synthetic END_<kind>.
 *  2. Normalization of the TwinCAT dialect the grammar excludes by design.
 *     Sixteen passes, each a hand-written scanner rather than a regex:
 *     compat_regex is POSIX-only and has neither lookahead nor a portable \b.
 *     Each pass reproduces its reference pattern's match semantics, including
 *     case sensitivity (constructor arguments and ARRAY ... OF are matched
 *     case-sensitively on purpose) and word boundaries, where bytes >= 0x80
 *     count as word characters (UTF-8 letters).
 *
 * Declaration-level passes (array initializers, constructor arguments) run
 * only inside VAR ... END_VAR regions, where statements cannot live: applied
 * to the whole unit they turned invalid statement code into a clean parse.
 *
 * Every pass preserves the number and order of newlines — deleted text gives
 * back the newlines it contained — so line N of the generated ST is still the
 * line the assembly map recorded, and definitions can be reported at their
 * real position in the XML file.
 */
#include "twincat_xml.h"

#include "foundation/mem_core.h" // per-file transient: freed inside one extraction call

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

enum {
    TC_BUF_INIT = 4096,
    TC_UTF8_BYTE = 0x80,
    TC_MAX_DEPTH = 64,
    TC_CDATA_OPEN_LEN = 9,    /* "<![CDATA[" */
    TC_CDATA_CLOSE_LEN = 3,   /* "]]>" */
    TC_COMMENT_OPEN_LEN = 4,  /* "<!--" */
    TC_COMMENT_CLOSE_LEN = 3, /* "-->" */
};

/* ── growable byte buffer ─────────────────────────────────────────────────── */

typedef struct {
    char *p;
    size_t len;
    size_t cap;
    bool oom;
} TcBuf;

static void tb_reserve(TcBuf *b, size_t extra) {
    if (b->oom) {
        return;
    }
    size_t need = b->len + extra + 1;
    if (b->p && need <= b->cap) {
        return;
    }
    size_t cap = b->cap ? b->cap : TC_BUF_INIT;
    while (cap < need) {
        cap *= 2;
    }
    char *np = (char *)cbm_realloc(CBM_MEM_CLASS_EXTRACT, b->p, cap);
    if (!np) {
        b->oom = true;
        return;
    }
    b->p = np;
    b->cap = cap;
    b->p[b->len] = '\0';
}

static void tb_put(TcBuf *b, const char *s, size_t n) {
    tb_reserve(b, n);
    if (b->oom) {
        return;
    }
    if (n > 0) {
        memcpy(b->p + b->len, s, n);
    }
    b->len += n;
    b->p[b->len] = '\0';
}

static void tb_putc(TcBuf *b, char c) {
    tb_put(b, &c, 1);
}

static void tb_free(TcBuf *b) {
    cbm_free(CBM_MEM_CLASS_EXTRACT, b->p);
    memset(b, 0, sizeof(*b));
}

/* ── line map ─────────────────────────────────────────────────────────────── */

typedef struct {
    uint32_t *v;
    uint32_t n;
    uint32_t cap;
    bool oom;
} TcLines;

static void tl_push(TcLines *l, uint32_t line) {
    if (l->oom) {
        return;
    }
    if (l->n == l->cap) {
        uint32_t cap = l->cap ? l->cap * 2 : (uint32_t)TC_BUF_INIT;
        uint32_t *nv =
            (uint32_t *)cbm_realloc(CBM_MEM_CLASS_EXTRACT, l->v, (size_t)cap * sizeof(uint32_t));
        if (!nv) {
            l->oom = true;
            return;
        }
        l->v = nv;
        l->cap = cap;
    }
    l->v[l->n++] = line;
}

/* ── character classes ────────────────────────────────────────────────────── */

static bool is_blank(char c) {
    return c == ' ' || c == '\t';
}

static bool is_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v';
}

static bool is_alpha_(char c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_';
}

static bool is_digit(char c) {
    return c >= '0' && c <= '9';
}

/* Regex \w on text: ASCII alnum, '_', and any UTF-8 byte (letters beyond ASCII). */
static bool is_word(char c) {
    return is_alpha_(c) || is_digit(c) || (unsigned char)c >= TC_UTF8_BYTE;
}

static char up(char c) {
    return (c >= 'a' && c <= 'z') ? (char)(c - 'a' + 'A') : c;
}

/* Case-insensitive match of an UPPERCASE ASCII literal at s[i]. */
static bool ci_at(const char *s, size_t n, size_t i, const char *lit) {
    for (size_t k = 0; lit[k]; k++) {
        if (i + k >= n || up(s[i + k]) != lit[k]) {
            return false;
        }
    }
    return true;
}

/* Case-sensitive match of a literal at s[i]. */
static bool cs_at(const char *s, size_t n, size_t i, const char *lit) {
    size_t len = strlen(lit);
    return i <= n && n - i >= len && memcmp(s + i, lit, len) == 0;
}

/* \b before a word character at i. */
static bool starts_word(const char *s, size_t i) {
    return i == 0 || !is_word(s[i - 1]);
}

/* \b after a word character ending at j. */
static bool ends_word(const char *s, size_t n, size_t j) {
    return j >= n || !is_word(s[j]);
}

static size_t skip_blanks(const char *s, size_t n, size_t i) {
    while (i < n && is_blank(s[i])) {
        i++;
    }
    return i;
}

/* [ \t]+ — returns the position after the run, or 0 when there is none
 * (0 is never a valid "after" position because i >= 1 whenever called). */
static size_t need_blanks(const char *s, size_t n, size_t i) {
    if (i >= n || !is_blank(s[i])) {
        return 0;
    }
    return skip_blanks(s, n, i);
}

static size_t word_end(const char *s, size_t n, size_t i) {
    while (i < n && is_word(s[i])) {
        i++;
    }
    return i;
}

/* Case-insensitive whole-span equality with one of a NULL-terminated list. */
static bool span_in(const char *s, size_t len, const char *const *list) {
    for (size_t k = 0; list[k]; k++) {
        if (strlen(list[k]) == len && ci_at(s, len, 0, list[k])) {
            return true;
        }
    }
    return false;
}

/* Length of an access modifier matched as a PREFIX at s[i], or 0. */
static size_t modifier_at(const char *s, size_t n, size_t i) {
    static const char *const MODS[] = {"PUBLIC", "PRIVATE", "PROTECTED", "INTERNAL", NULL};
    for (size_t k = 0; MODS[k]; k++) {
        if (ci_at(s, n, i, MODS[k])) {
            return strlen(MODS[k]);
        }
    }
    return 0;
}

static const char *const VAR_SECTIONS[] = {"VAR",      "VAR_INPUT", "VAR_OUTPUT", "VAR_IN_OUT",
                                           "VAR_STAT", "VAR_INST",  "VAR_GLOBAL", NULL};

/* ── copy-with-replacements cursor ────────────────────────────────────────── */

typedef struct {
    TcBuf *out;
    const char *s;
    size_t from; /* first input byte not yet copied */
} TcCopy;

static void cp_flush(TcCopy *c, size_t upto) {
    if (upto > c->from) {
        tb_put(c->out, c->s + c->from, upto - c->from);
    }
    if (upto > c->from) {
        c->from = upto;
    }
}

/* Replace s[start, end) with rep, giving back every newline the span held. */
static void cp_replace(TcCopy *c, size_t start, size_t end, const char *rep, size_t rep_len) {
    cp_flush(c, start);
    tb_put(c->out, rep, rep_len);
    for (size_t q = start; q < end; q++) {
        if (c->s[q] == '\n') {
            tb_putc(c->out, '\n');
        }
    }
    c->from = end;
}

typedef void (*TcPass)(TcBuf *out, const char *s, size_t n);

/* ── normalization passes ─────────────────────────────────────────────────── */

/* A line holding only a {pragma}, but never one carrying a comment delimiter:
 * "{*) x (*}" closes and reopens a block comment, so dropping it would turn
 * dead code live. The line is blanked, not removed. */
static void pass_pragma(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    size_t i = 0;
    while (i < n) {
        size_t eol = i;
        while (eol < n && s[eol] != '\n') {
            eol++;
        }
        size_t j = skip_blanks(s, eol, i);
        if (eol < n && j < eol && s[j] == '{') {
            size_t k = j + 1;
            while (k < eol && s[k] != '}') {
                k++;
            }
            bool comment = false;
            for (size_t q = j + 1; q + 1 < k; q++) {
                if ((s[q] == '(' && s[q + 1] == '*') || (s[q] == '*' && s[q + 1] == ')')) {
                    comment = true;
                    break;
                }
            }
            if (k < eol && !comment) {
                size_t m = skip_blanks(s, eol, k + 1);
                if (m < eol && s[m] == '\r') {
                    m++;
                }
                if (m == eol) {
                    cp_replace(&c, i, eol, "", 0);
                }
            }
        }
        i = eol < n ? eol + 1 : n;
    }
    cp_flush(&c, n);
}

/* Integer base types an enum may carry: "TYPE E : ( ... ) UINT;". */
static const char *const ENUM_BASES[] = {"UINT", "INT",   "BYTE",  "WORD", "DWORD", "DINT",
                                         "SINT", "USINT", "UDINT", "LINT", "ULINT", NULL};

/* "UNION" / "END_UNION" -> "STRUCT" / "END_STRUCT": the grammar has no union,
 * and for the graph a union's members are fields of the type like a struct's. */
static void pass_union(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'E' && starts_word(s, i) && ci_at(s, n, i, "END_UNION") &&
            ends_word(s, n, i + 9)) {
            cp_replace(&c, i, i + 9, "END_STRUCT", 10);
            i += 9;
            continue;
        }
        if (up(s[i]) == 'U' && starts_word(s, i) && ci_at(s, n, i, "UNION") &&
            ends_word(s, n, i + 5)) {
            cp_replace(&c, i, i + 5, "STRUCT", 6);
            i += 5;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* END_STRUCT not followed by ';' gets one. */
static void pass_struct_semi(TcBuf *out, const char *s, size_t n) {
    static const char KW[] = "END_STRUCT";
    const size_t kl = sizeof(KW) - 1;
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'E' && starts_word(s, i) && ci_at(s, n, i, KW) && ends_word(s, n, i + kl)) {
            size_t j = i + kl;
            while (j < n && is_space(s[j])) {
                j++;
            }
            if (j >= n || s[j] != ';') {
                cp_replace(&c, i, i + kl, "END_STRUCT;", kl + 1);
            }
            i += kl;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* Enum base type ") UINT;" -> ");". */
static void pass_enum_base(TcBuf *out, const char *s, size_t n) {

    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n; i++) {
        if (s[i] != ')') {
            continue;
        }
        size_t j = skip_blanks(s, n, i + 1);
        size_t k = word_end(s, n, j);
        if (k > j && span_in(s + j, k - j, ENUM_BASES)) {
            size_t m = skip_blanks(s, n, k);
            if (m < n && s[m] == ';') {
                cp_replace(&c, i, m + 1, ");", 2);
                i = m;
            }
        }
    }
    cp_flush(&c, n);
}

/* "AT %I*" / "AT %QX0.1" hardware address bindings are dropped. */
static void pass_at_address(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'A' && starts_word(s, i) && ci_at(s, n, i, "AT")) {
            size_t j = need_blanks(s, n, i + 2);
            if (j && j + 1 < n && s[j] == '%' &&
                (up(s[j + 1]) == 'I' || up(s[j + 1]) == 'Q' || up(s[j + 1]) == 'M')) {
                size_t k = j + 2;
                while (k < n && (is_alpha_(s[k]) || is_digit(s[k]) || s[k] == '.' || s[k] == '*') &&
                       s[k] != '_') {
                    k++;
                }
                cp_replace(&c, i, k, "", 0);
                i = k;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

static void pass_reference_to(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'R' && starts_word(s, i) && ci_at(s, n, i, "REFERENCE")) {
            size_t j = need_blanks(s, n, i + strlen("REFERENCE"));
            if (j && ci_at(s, n, j, "TO") && ends_word(s, n, j + 2)) {
                cp_replace(&c, i, j + 2, "POINTER TO", strlen("POINTER TO"));
                i = j + 2;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

static void pass_var_stat(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'V' && starts_word(s, i) &&
            (ci_at(s, n, i, "VAR_STAT") || ci_at(s, n, i, "VAR_INST")) &&
            ends_word(s, n, i + strlen("VAR_STAT"))) {
            size_t e = i + strlen("VAR_STAT");
            cp_replace(&c, i, e, "VAR", 3);
            i = e;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* "VAR [RETAIN] PERSISTENT" keeps the section keyword only. */
static void pass_persistent(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) != 'V' || !starts_word(s, i) || !ci_at(s, n, i, "VAR")) {
            i++;
            continue;
        }
        size_t k = word_end(s, n, i);
        if (!span_in(s + i, k - i, VAR_SECTIONS)) {
            i = k;
            continue;
        }
        size_t j = need_blanks(s, n, k);
        size_t end = 0;
        if (j) {
            size_t r = ci_at(s, n, j, "RETAIN") ? need_blanks(s, n, j + strlen("RETAIN")) : 0;
            if (r && ci_at(s, n, r, "PERSISTENT") && ends_word(s, n, r + strlen("PERSISTENT"))) {
                end = r + strlen("PERSISTENT");
            } else if (ci_at(s, n, j, "PERSISTENT") && ends_word(s, n, j + strlen("PERSISTENT"))) {
                end = j + strlen("PERSISTENT");
            }
        }
        if (end) {
            cp_replace(&c, k, end, "", 0);
            i = end;
        } else {
            i = k;
        }
    }
    cp_flush(&c, n);
}

static void pass_and_then(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (starts_word(s, i)) {
            if (ci_at(s, n, i, "AND_THEN") && ends_word(s, n, i + strlen("AND_THEN"))) {
                cp_replace(&c, i, i + strlen("AND_THEN"), "AND", 3);
                i += strlen("AND_THEN");
                continue;
            }
            if (ci_at(s, n, i, "OR_ELSE") && ends_word(s, n, i + strlen("OR_ELSE"))) {
                cp_replace(&c, i, i + strlen("OR_ELSE"), "OR", 2);
                i += strlen("OR_ELSE");
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* ── VAR ... END_VAR regions ──────────────────────────────────────────────── */

static bool line_opens_var(const char *s, size_t eol, size_t i) {
    size_t j = skip_blanks(s, eol, i);
    if (!ci_at(s, eol, j, "VAR")) {
        return false;
    }
    size_t k = word_end(s, eol, j);
    return span_in(s + j, k - j, VAR_SECTIONS);
}

static bool line_closes_var(const char *s, size_t eol, size_t i) {
    size_t j = skip_blanks(s, eol, i);
    return ci_at(s, eol, j, "END_VAR") && ends_word(s, eol, j + strlen("END_VAR"));
}

/* Apply `fn` to every VAR ... END_VAR region (open and close lines included);
 * copy everything else unchanged. An unterminated region runs to the end. */
static void in_var_blocks(TcBuf *out, const char *s, size_t n, TcPass fn) {
    bool inside = false;
    size_t region = 0;
    size_t i = 0;
    while (i < n) {
        size_t eol = i;
        while (eol < n && s[eol] != '\n') {
            eol++;
        }
        size_t next = eol < n ? eol + 1 : n;
        if (!inside) {
            if (line_opens_var(s, eol, i)) {
                inside = true;
                region = i;
            } else {
                tb_put(out, s + i, next - i);
            }
        } else if (line_closes_var(s, eol, i)) {
            fn(out, s + region, next - region);
            inside = false;
        }
        i = next;
    }
    if (inside) {
        fn(out, s + region, n - region);
    }
}

/* ":= [ ... ]" array initializer before ';' is dropped. */
static void region_arr_init(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i + 1 < n; i++) {
        if (s[i] != ':' || s[i + 1] != '=') {
            continue;
        }
        size_t j = i + 2;
        while (j < n && is_space(s[j]) && s[j] != '\f' && s[j] != '\v') {
            j++;
        }
        if (j >= n || s[j] != '[') {
            continue;
        }
        size_t k = j + 1;
        while (k < n && s[k] != ']') {
            k++;
        }
        if (k >= n) {
            continue;
        }
        size_t m = skip_blanks(s, n, k + 1);
        if (m < n && s[m] == ';') {
            cp_replace(&c, i, m, "", 0);
            i = m - 1;
        }
    }
    cp_flush(&c, n);
}

/* Constructor arguments at a line start: "name : [ARRAY[..] OF] Type(args);"
 * -> "name : [ARRAY[..] OF] Type;". One level of nested parentheses, args may
 * span lines. ARRAY/OF are case-sensitive, as in the reference pattern.
 * Returns the index after ';' or 0; g1_end = end of the kept head,
 * g2_start = first byte after ')'. */
static size_t ctor_match(const char *s, size_t n, size_t i, size_t *g1_end, size_t *g2_start) {
    size_t p = skip_blanks(s, n, i);
    if (p >= n || !is_alpha_(s[p])) {
        return 0;
    }
    p = word_end(s, n, p + 1);
    p = skip_blanks(s, n, p);
    if (p >= n || s[p] != ':') {
        return 0;
    }
    p = skip_blanks(s, n, p + 1);
    if (cs_at(s, n, p, "ARRAY")) {
        size_t q = skip_blanks(s, n, p + strlen("ARRAY"));
        if (q < n && s[q] == '[') {
            q++;
            while (q < n && s[q] != ']' && s[q] != '\n') {
                q++;
            }
            if (q < n && s[q] == ']') {
                q = skip_blanks(s, n, q + 1);
                if (cs_at(s, n, q, "OF")) {
                    p = skip_blanks(s, n, q + 2);
                }
            }
        }
    }
    if (p >= n || !is_alpha_(s[p])) {
        return 0;
    }
    p++;
    while (p < n && (is_word(s[p]) || s[p] == '.')) {
        p++;
    }
    *g1_end = p;
    p = skip_blanks(s, n, p);
    if (p >= n || s[p] != '(') {
        return 0;
    }
    size_t q = p + 1;
    for (;;) {
        if (q >= n) {
            return 0;
        }
        if (s[q] == ')') {
            break;
        }
        if (s[q] == '(') {
            size_t r = q + 1;
            while (r < n && s[r] != '(' && s[r] != ')') {
                r++;
            }
            if (r >= n || s[r] != ')') {
                return 0;
            }
            q = r + 1;
            continue;
        }
        q++;
    }
    *g2_start = q + 1;
    size_t m = skip_blanks(s, n, q + 1);
    if (m >= n || s[m] != ';') {
        return 0;
    }
    return m + 1;
}

static void region_ctor_args(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    size_t i = 0; /* always a line start */
    while (i < n) {
        size_t g1_end = 0;
        size_t g2_start = 0;
        size_t end = ctor_match(s, n, i, &g1_end, &g2_start);
        size_t resume = i;
        if (end) {
            /* head, then " ;" tail, then the newlines the dropped args held */
            cp_flush(&c, g1_end);
            tb_put(out, s + g2_start, end - g2_start);
            for (size_t q = g1_end; q < g2_start; q++) {
                if (s[q] == '\n') {
                    tb_putc(out, '\n');
                }
            }
            c.from = end;
            resume = end;
        }
        while (resume < n && s[resume] != '\n') {
            resume++;
        }
        i = resume < n ? resume + 1 : n;
    }
    cp_flush(&c, n);
}

static void pass_arr_init(TcBuf *out, const char *s, size_t n) {
    in_var_blocks(out, s, n, region_arr_init);
}

static void pass_ctor_args(TcBuf *out, const char *s, size_t n) {
    in_var_blocks(out, s, n, region_ctor_args);
}

/* ── remaining passes ─────────────────────────────────────────────────────── */

static void pass_array_star(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'A' && starts_word(s, i) && ci_at(s, n, i, "ARRAY")) {
            size_t j = skip_blanks(s, n, i + strlen("ARRAY"));
            if (j < n && s[j] == '[') {
                j = skip_blanks(s, n, j + 1);
                if (j < n && s[j] == '*') {
                    j = skip_blanks(s, n, j + 1);
                    if (j < n && s[j] == ']') {
                        cp_replace(&c, i, j + 1, "ARRAY[1..1]", strlen("ARRAY[1..1]"));
                        i = j + 1;
                        continue;
                    }
                }
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* STRING[80] / WSTRING[80] -> STRING / WSTRING (keeps the original spelling). */
static void pass_str_len(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t g = 0;
        if (starts_word(s, i)) {
            if (up(s[i]) == 'W' && ci_at(s, n, i + 1, "STRING")) {
                g = strlen("WSTRING");
            } else if (ci_at(s, n, i, "STRING")) {
                g = strlen("STRING");
            }
        }
        if (g) {
            size_t j = skip_blanks(s, n, i + g);
            if (j < n && s[j] == '[') {
                size_t k = j + 1;
                while (k < n && s[k] != ']' && s[k] != '\n') {
                    k++;
                }
                if (k < n && s[k] == ']') {
                    cp_flush(&c, i + g);
                    c.from = k + 1;
                    i = k + 1;
                    continue;
                }
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* "FUNCTION_BLOCK PUBLIC X" / "PROGRAM INTERNAL X" -> keyword + one space + X. */
static void pass_pou_access(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t kl = 0;
        if (starts_word(s, i)) {
            if (ci_at(s, n, i, "PROGRAM")) {
                kl = strlen("PROGRAM");
            } else if (ci_at(s, n, i, "FUNCTION_BLOCK")) {
                kl = strlen("FUNCTION_BLOCK");
            }
        }
        if (kl) {
            size_t j = need_blanks(s, n, i + kl);
            size_t ml = j ? modifier_at(s, n, j) : 0;
            size_t m = ml ? need_blanks(s, n, j + ml) : 0;
            if (m && m < n && is_alpha_(s[m])) {
                cp_flush(&c, i + kl);
                tb_putc(out, ' ');
                c.from = m;
                i = m;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* A PROGRAM that owns METHODs or PROPERTYs is only valid as a FUNCTION_BLOCK. */
static void pass_program_as_fb(TcBuf *out, const char *s, size_t n) {
    bool has_member = false;
    size_t hdr = 0;
    size_t name_start = 0;
    size_t name_end = 0;
    bool has_hdr = false;
    for (size_t i = 0; i < n;) {
        size_t eol = i;
        while (eol < n && s[eol] != '\n') {
            eol++;
        }
        size_t j = skip_blanks(s, eol, i);
        if ((ci_at(s, eol, j, "METHOD") && ends_word(s, eol, j + strlen("METHOD"))) ||
            (ci_at(s, eol, j, "PROPERTY") && ends_word(s, eol, j + strlen("PROPERTY")))) {
            has_member = true;
        }
        if (!has_hdr && ci_at(s, eol, i, "PROGRAM")) {
            size_t k = need_blanks(s, eol, i + strlen("PROGRAM"));
            if (k && k < eol && is_alpha_(s[k])) {
                has_hdr = true;
                hdr = i;
                name_start = k;
                name_end = word_end(s, eol, k + 1);
            }
        }
        i = eol < n ? eol + 1 : n;
    }
    if (!has_member || !has_hdr) {
        tb_put(out, s, n);
        return;
    }
    TcCopy c = {out, s, 0};
    cp_flush(&c, hdr);
    tb_put(out, "FUNCTION_BLOCK ", strlen("FUNCTION_BLOCK "));
    tb_put(out, s + name_start, name_end - name_start);
    c.from = name_end;
    for (size_t i = name_end; i < n;) {
        if (s[i] == 'E' && cs_at(s, n, i, "END_PROGRAM")) {
            cp_replace(&c, i, i + strlen("END_PROGRAM"), "END_FUNCTION_BLOCK",
                       strlen("END_FUNCTION_BLOCK"));
            i += strlen("END_PROGRAM");
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* ABSTRACT / FINAL after FUNCTION_BLOCK, METHOD or PROPERTY (and any access
 * modifiers) are dropped. */
static void pass_modifier(TcBuf *out, const char *s, size_t n) {
    static const char *const KWS[] = {"FUNCTION_BLOCK", "METHOD", "PROPERTY", NULL};
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t kl = 0;
        if (starts_word(s, i)) {
            for (size_t k = 0; KWS[k] && !kl; k++) {
                if (ci_at(s, n, i, KWS[k])) {
                    kl = strlen(KWS[k]);
                }
            }
        }
        if (!kl) {
            i++;
            continue;
        }
        size_t p = i + kl;
        for (;;) {
            size_t q = need_blanks(s, n, p);
            size_t ml = q ? modifier_at(s, n, q) : 0;
            if (ml && q + ml < n && is_blank(s[q + ml])) {
                p = q + ml;
                continue;
            }
            break;
        }
        size_t q = need_blanks(s, n, p);
        size_t end = 0;
        if (q && ci_at(s, n, q, "ABSTRACT") && ends_word(s, n, q + strlen("ABSTRACT"))) {
            end = q + strlen("ABSTRACT");
        } else if (q && ci_at(s, n, q, "FINAL") && ends_word(s, n, q + strlen("FINAL"))) {
            end = q + strlen("FINAL");
        }
        if (end) {
            cp_replace(&c, p, end, "", 0);
            i = end;
        } else {
            i += kl;
        }
    }
    cp_flush(&c, n);
}

/* "TYPE T_X EXTENDS T_Base :" -> "TYPE T_X :". */
static void pass_type_extends(TcBuf *out, const char *s, size_t n) {
    TcCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'T' && starts_word(s, i) && ci_at(s, n, i, "TYPE")) {
            size_t j = need_blanks(s, n, i + strlen("TYPE"));
            if (j && j < n && is_alpha_(s[j])) {
                size_t k = word_end(s, n, j + 1);
                size_t m = need_blanks(s, n, k);
                size_t b =
                    (m && ci_at(s, n, m, "EXTENDS")) ? need_blanks(s, n, m + strlen("EXTENDS")) : 0;
                if (b && b < n && is_alpha_(s[b])) {
                    size_t e = b + 1;
                    while (e < n && (is_word(s[e]) || s[e] == '.')) {
                        e++;
                    }
                    cp_replace(&c, k, e, "", 0);
                    i = e;
                    continue;
                }
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

char *cbm_twincat_normalize(const char *src, int len, int *out_len) {
    static const TcPass PASSES[] = {
        pass_pragma,       pass_union,        pass_struct_semi, pass_enum_base,  pass_at_address,

        pass_reference_to, pass_var_stat,     pass_persistent,  pass_and_then,   pass_arr_init,
        pass_ctor_args,    pass_array_star,   pass_str_len,     pass_pou_access, pass_program_as_fb,
        pass_modifier,     pass_type_extends,
    };
    TcBuf cur = {0};
    tb_put(&cur, src ? src : "", (src && len > 0) ? (size_t)len : 0);
    for (size_t k = 0; k < sizeof(PASSES) / sizeof(PASSES[0]) && !cur.oom; k++) {
        TcBuf next = {0};
        tb_reserve(&next, cur.len);
        PASSES[k](&next, cur.p, cur.len);
        tb_put(&next, "", 0);
        if (next.oom) {
            tb_free(&next);
            tb_free(&cur);
            return NULL;
        }
        tb_free(&cur);
        cur = next;
    }
    if (cur.oom) {
        tb_free(&cur);
        return NULL;
    }
    if (out_len) {
        *out_len = (int)cur.len;
    }
    return cur.p;
}

/* ── XML model ────────────────────────────────────────────────────────────── */

typedef enum { TC_OBJ, TC_METHOD, TC_PROPERTY, TC_GET, TC_SET } TcKind;

typedef struct {
    TcKind kind;
    int parent;
    TcBuf decl;
    uint32_t decl_line; /* line where the declaration's character data starts */
    bool decl_seen;     /* first <Declaration> child only */
    TcBuf impl;
    uint32_t impl_line;
    bool impl_seen; /* first <Implementation><ST> only */
    uint32_t open_line;
    uint32_t close_line;
} TcNode;

typedef enum { ROLE_NONE, ROLE_NODE, ROLE_DECL, ROLE_IMPL, ROLE_ST } TcRole;

typedef struct {
    TcRole role;
    int node;
    bool child_seen; /* character data after a child element is not .text */
} TcFrame;

typedef struct {
    TcNode *nodes;
    int count;
    int cap;
    int obj;
    bool obj_is_type_or_gvl; /* DUT or GVL: declaration only */
    bool oom;
} TcModel;

static int model_add(TcModel *m, TcKind kind, int parent, uint32_t line) {
    if (m->count == m->cap) {
        int cap = m->cap ? m->cap * 2 : TC_MAX_DEPTH;
        TcNode *nn =
            (TcNode *)cbm_realloc(CBM_MEM_CLASS_EXTRACT, m->nodes, (size_t)cap * sizeof(TcNode));
        if (!nn) {
            m->oom = true;
            return -1;
        }
        m->nodes = nn;
        m->cap = cap;
    }
    TcNode *nd = &m->nodes[m->count];
    memset(nd, 0, sizeof(*nd));
    nd->kind = kind;
    nd->parent = parent;
    nd->open_line = line;
    return m->count++;
}

static void model_free(TcModel *m) {
    for (int i = 0; i < m->count; i++) {
        tb_free(&m->nodes[i].decl);
        tb_free(&m->nodes[i].impl);
    }
    cbm_free(CBM_MEM_CLASS_EXTRACT, m->nodes);
    memset(m, 0, sizeof(*m));
}

static size_t find_str(const char *s, size_t n, size_t from, const char *needle) {
    size_t len = strlen(needle);
    for (size_t i = from; i + len <= n; i++) {
        if (s[i] == needle[0] && memcmp(s + i, needle, len) == 0) {
            return i;
        }
    }
    return n;
}

static bool name_is(const char *name, size_t len, const char *lit) {
    return strlen(lit) == len && memcmp(name, lit, len) == 0;
}

/* Character data for the frame on top of the stack. */
static void deliver_text(TcModel *m, const TcFrame *top, const char *s, size_t len, uint32_t line,
                         bool raw) {
    if (!top || top->child_seen || (top->role != ROLE_DECL && top->role != ROLE_ST)) {
        return;
    }
    TcNode *nd = &m->nodes[top->node];
    TcBuf *b = top->role == ROLE_DECL ? &nd->decl : &nd->impl;
    uint32_t *first = top->role == ROLE_DECL ? &nd->decl_line : &nd->impl_line;
    if (b->len == 0 && *first == 0) {
        *first = line;
    }
    if (!raw) {
        tb_put(b, s, len);
        return;
    }
    static const struct {
        const char *ent;
        char ch;
    } ENTS[] = {{"&lt;", '<'}, {"&gt;", '>'}, {"&amp;", '&'}, {"&quot;", '"'}, {"&apos;", '\''}};
    for (size_t i = 0; i < len; i++) {
        bool done = false;
        if (s[i] == '&') {
            for (size_t e = 0; e < sizeof(ENTS) / sizeof(ENTS[0]); e++) {
                if (cs_at(s, len, i, ENTS[e].ent)) {
                    tb_putc(b, ENTS[e].ch);
                    i += strlen(ENTS[e].ent) - 1;
                    done = true;
                    break;
                }
            }
        }
        if (!done) {
            tb_putc(b, s[i]);
        }
    }
}

/* Parse the TwinCAT object XML into a model. Lenient: unknown elements are
 * skipped, mismatched close tags simply pop. Returns false only on truncated
 * markup or allocation failure. */
static bool model_parse(TcModel *m, const char *s, size_t n) {
    TcFrame stack[TC_MAX_DEPTH];
    int depth = 0;
    int overflow = 0; /* elements nested deeper than TC_MAX_DEPTH */
    uint32_t line = 1;
    size_t i = 0;
    m->obj = -1;
    if (n >= 3 && (unsigned char)s[0] == 0xEF && (unsigned char)s[1] == 0xBB &&
        (unsigned char)s[2] == 0xBF) {
        i = 3;
    }
    while (i < n && !m->oom) {
        size_t lt = i;
        while (lt < n && s[lt] != '<') {
            lt++;
        }
        const TcFrame *top = (depth > 0 && !overflow) ? &stack[depth - 1] : NULL;
        if (lt > i) {
            deliver_text(m, top, s + i, lt - i, line, true);
            for (size_t q = i; q < lt; q++) {
                line += s[q] == '\n';
            }
        }
        if (lt >= n) {
            break;
        }
        uint32_t tag_line = line;
        size_t end;
        if (cs_at(s, n, lt, "<![CDATA[")) {
            size_t cs = lt + TC_CDATA_OPEN_LEN;
            size_t ce = find_str(s, n, cs, "]]>");
            if (ce >= n) {
                return false;
            }
            deliver_text(m, top, s + cs, ce - cs, line, false);
            end = ce + TC_CDATA_CLOSE_LEN;
        } else if (cs_at(s, n, lt, "<!--")) {
            size_t ce = find_str(s, n, lt + TC_COMMENT_OPEN_LEN, "-->");
            if (ce >= n) {
                return false;
            }
            end = ce + TC_COMMENT_CLOSE_LEN;
        } else if (cs_at(s, n, lt, "<?")) {
            size_t ce = find_str(s, n, lt + 2, "?>");
            if (ce >= n) {
                return false;
            }
            end = ce + 2;
        } else {
            /* element tag: find '>' outside quoted attribute values */
            size_t gt = lt + 1;
            char quote = 0;
            while (gt < n && (quote || s[gt] != '>')) {
                if (quote && s[gt] == quote) {
                    quote = 0;
                } else if (!quote && (s[gt] == '"' || s[gt] == '\'')) {
                    quote = s[gt];
                }
                gt++;
            }
            if (gt >= n) {
                return false;
            }
            end = gt + 1;
            if (s[lt + 1] == '!') {
                /* <!DOCTYPE ...> */
            } else if (s[lt + 1] == '/') {
                if (overflow > 0) {
                    overflow--;
                } else if (depth > 0) {
                    const TcFrame *f = &stack[--depth];
                    if (f->role == ROLE_NODE) {
                        m->nodes[f->node].close_line = tag_line;
                    }
                }
            } else {
                size_t ns = lt + 1;
                size_t ne = ns;
                while (ne < gt && !is_space(s[ne]) && s[ne] != '/' && s[ne] != '>') {
                    ne++;
                }
                bool self_closing = s[gt - 1] == '/';
                const char *name = s + ns;
                size_t nl = ne - ns;
                TcFrame f = {ROLE_NONE, -1, false};
                TcFrame *parent = (depth > 0 && !overflow) ? &stack[depth - 1] : NULL;
                if (parent) {
                    parent->child_seen = true;
                }
                if (depth == 1 && !overflow && m->obj < 0 &&
                    (name_is(name, nl, "POU") || name_is(name, nl, "DUT") ||
                     name_is(name, nl, "GVL") || name_is(name, nl, "Itf"))) {
                    m->obj = model_add(m, TC_OBJ, -1, tag_line);
                    m->obj_is_type_or_gvl = name_is(name, nl, "DUT") || name_is(name, nl, "GVL");
                    f = (TcFrame){ROLE_NODE, m->obj, false};
                } else if (parent && parent->role == ROLE_NODE) {
                    int pi = parent->node;
                    TcKind pk = m->nodes[pi].kind;
                    int child = -1;
                    if (name_is(name, nl, "Declaration")) {
                        if (!m->nodes[pi].decl_seen) {
                            m->nodes[pi].decl_seen = true;
                            f = (TcFrame){ROLE_DECL, pi, false};
                        }
                    } else if (name_is(name, nl, "Implementation")) {
                        f = (TcFrame){ROLE_IMPL, pi, false};
                    } else if (pk == TC_OBJ && name_is(name, nl, "Method")) {
                        child = model_add(m, TC_METHOD, pi, tag_line);
                    } else if (pk == TC_OBJ && name_is(name, nl, "Property")) {
                        child = model_add(m, TC_PROPERTY, pi, tag_line);
                    } else if (pk == TC_PROPERTY && name_is(name, nl, "Get")) {
                        child = model_add(m, TC_GET, pi, tag_line);
                    } else if (pk == TC_PROPERTY && name_is(name, nl, "Set")) {
                        child = model_add(m, TC_SET, pi, tag_line);
                    }
                    if (child >= 0) {
                        f = (TcFrame){ROLE_NODE, child, false};
                    }
                } else if (parent && parent->role == ROLE_IMPL && name_is(name, nl, "ST")) {
                    int pi = parent->node;
                    if (!m->nodes[pi].impl_seen) {
                        m->nodes[pi].impl_seen = true;
                        f = (TcFrame){ROLE_ST, pi, false};
                    }
                }
                if (m->oom) {
                    return false;
                }
                if (self_closing) {
                    if (f.role == ROLE_NODE) {
                        for (size_t q = lt; q < gt; q++) {
                            tag_line += s[q] == '\n';
                        }
                        m->nodes[f.node].close_line = tag_line;
                    }
                } else if (overflow > 0 || depth >= TC_MAX_DEPTH) {
                    overflow++;
                } else {
                    stack[depth++] = f;
                }
            }
        }
        for (size_t q = lt; q < end; q++) {
            line += s[q] == '\n';
        }
        i = end;
    }
    return !m->oom;
}

/* ── assembly ─────────────────────────────────────────────────────────────── */

typedef struct {
    TcBuf out;
    TcLines map;
} TcAsm;

/* Python's nl(): the text, plus a newline unless empty or already ending in one. */
static void asm_text(TcAsm *a, const char *p, size_t len, uint32_t first_line) {
    if (len == 0) {
        return;
    }
    uint32_t line = first_line;
    for (size_t k = 0; k < len; k++) {
        if (p[k] == '\n') {
            tl_push(&a->map, line);
            line++;
        }
    }
    tb_put(&a->out, p, len);
    if (p[len - 1] != '\n') {
        tb_putc(&a->out, '\n');
        tl_push(&a->map, line);
    }
}

/* A synthetic line (keyword + '\n'), attributed to one XML line. */
static void asm_line(TcAsm *a, const char *lit, uint32_t line) {
    tb_put(&a->out, lit, strlen(lit));
    tb_putc(&a->out, '\n');
    tl_push(&a->map, line);
}

static uint32_t close_or_open(const TcNode *nd) {
    return nd->close_line ? nd->close_line : nd->open_line;
}

/* A leading access-modifier line on an accessor declaration is dropped
 * (reference: "^[ \t]*(PUBLIC|PRIVATE|PROTECTED|INTERNAL)[ \t]*\r?\n" at the
 * very start only). Its newline is kept. */
static void asm_accessor_decl(TcAsm *a, const TcNode *acc) {
    const char *p = acc->decl.p;
    size_t n = acc->decl.len;
    size_t j = skip_blanks(p, n, 0);
    size_t ml = modifier_at(p, n, j);
    if (ml) {
        size_t k = skip_blanks(p, n, j + ml);
        if (k < n && p[k] == '\r') {
            k++;
        }
        if (k < n && p[k] == '\n') {
            tb_putc(&a->out, '\n');
            tl_push(&a->map, acc->decl_line);
            asm_text(a, p + k + 1, n - k - 1, acc->decl_line + 1);
            return;
        }
    }
    asm_text(a, p, n, acc->decl_line);
}

typedef struct {
    const char *kw;
    const char *end_kw;
} TcPouKind;

static const TcPouKind POU_KINDS[] = {
    {"FUNCTION_BLOCK", "END_FUNCTION_BLOCK"},
    {"INTERFACE", "END_INTERFACE"},
    {"PROGRAM", "END_PROGRAM"},
    {"FUNCTION", "END_FUNCTION"},
    {"TYPE", "END_TYPE"},
    {"VAR_GLOBAL", "END_VAR"},
};

static bool span_contains(const char *s, size_t n, const char *needle) {
    return find_str(s, n, 0, needle) < n;
}

/* The declaration keyword: first line that is not blank, a comment or a pragma. */
static const TcPouKind *kind_of(const char *d, size_t n) {
    bool in_block = false;
    size_t i = 0;
    while (i < n) {
        size_t eol = i;
        while (eol < n && d[eol] != '\n') {
            eol++;
        }
        size_t a = i;
        size_t b = eol;
        while (a < b && is_space(d[a])) {
            a++;
        }
        while (b > a && is_space(d[b - 1])) {
            b--;
        }
        i = eol < n ? eol + 1 : n;
        const char *ln = d + a;
        size_t len = b - a;
        if (in_block) {
            if (span_contains(ln, len, "*)")) {
                in_block = false;
            }
            continue;
        }
        if (cs_at(ln, len, 0, "(*")) {
            if (!span_contains(ln, len, "*)")) {
                in_block = true;
            }
            continue;
        }
        if (len == 0 || cs_at(ln, len, 0, "//") || ln[0] == '{') {
            continue;
        }
        for (size_t k = 0; k < sizeof(POU_KINDS) / sizeof(POU_KINDS[0]); k++) {
            if (ci_at(ln, len, 0, POU_KINDS[k].kw)) {
                size_t kl = strlen(POU_KINDS[k].kw);
                char next = kl < len ? up(ln[kl]) : ' ';
                if (!is_alpha_(next) && !is_digit(next)) {
                    return &POU_KINDS[k];
                }
            }
        }
        return NULL;
    }
    return NULL;
}

static bool ci_contains(const char *s, size_t n, const char *lit) {
    size_t len = strlen(lit);
    for (size_t i = 0; i + len <= n; i++) {
        if (ci_at(s, n, i, lit)) {
            return true;
        }
    }
    return false;
}

static void assemble(TcAsm *a, const TcModel *m, const TcPouKind *kind) {
    const TcNode *obj = &m->nodes[m->obj];
    asm_text(a, obj->decl.p, obj->decl.len, obj->decl_line);
    if (m->obj_is_type_or_gvl) {
        if (!ci_contains(obj->decl.p, obj->decl.len, kind->end_kw)) {
            asm_line(a, kind->end_kw, close_or_open(obj));
        }
        return;
    }
    for (int i = 0; i < m->count; i++) {
        const TcNode *md = &m->nodes[i];
        if (md->kind != TC_METHOD || md->parent != m->obj) {
            continue;
        }
        asm_text(a, md->decl.p, md->decl.len, md->decl_line);
        asm_text(a, md->impl.p, md->impl.len, md->impl_line);
        asm_line(a, "END_METHOD", close_or_open(md));
    }
    for (int i = 0; i < m->count; i++) {
        const TcNode *pr = &m->nodes[i];
        if (pr->kind != TC_PROPERTY || pr->parent != m->obj) {
            continue;
        }
        asm_text(a, pr->decl.p, pr->decl.len, pr->decl_line);
        bool seen = false;
        static const struct {
            TcKind kind;
            const char *kw;
            const char *end_kw;
        } ACCESSORS[] = {{TC_GET, "GET", "END_GET"}, {TC_SET, "SET", "END_SET"}};
        for (size_t t = 0; t < sizeof(ACCESSORS) / sizeof(ACCESSORS[0]); t++) {
            for (int j = 0; j < m->count; j++) {
                const TcNode *acc = &m->nodes[j];
                if (acc->kind != ACCESSORS[t].kind || acc->parent != i) {
                    continue;
                }
                seen = true;
                asm_line(a, ACCESSORS[t].kw, acc->open_line);
                asm_accessor_decl(a, acc);
                asm_text(a, acc->impl.p, acc->impl.len, acc->impl_line);
                asm_line(a, ACCESSORS[t].end_kw, close_or_open(acc));
            }
        }
        if (!seen) {
            /* An ABSTRACT property has no accessor in the XML, but a PROPERTY
             * without GET/SET is invalid ST. */
            asm_line(a, "GET", close_or_open(pr));
            asm_line(a, "END_GET", close_or_open(pr));
        }
        asm_line(a, "END_PROPERTY", close_or_open(pr));
    }
    asm_text(a, obj->impl.p, obj->impl.len, obj->impl_line);
    asm_line(a, kind->end_kw, close_or_open(obj));
}

/* Record every enum base type the normalizer is about to strip, keyed by the
 * 1-based line of its ")" in the assembled ST. Every normalization pass keeps
 * newline count and order, so the line survives into the parsed text and lets
 * cbm.c hand the base back to the enum's members. Allocation failure only
 * loses the bases (members then keep the grammar's INT default). */
static void collect_enum_bases(const char *s, size_t n, CBMTwinCATUnit *out) {
    uint32_t line = 1;
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '\n') {
            line++;
            continue;
        }
        if (s[i] != ')') {
            continue;
        }
        size_t j = skip_blanks(s, n, i + 1);
        size_t k = word_end(s, n, j);
        if (k <= j || !span_in(s + j, k - j, ENUM_BASES)) {
            continue;
        }
        size_t m = skip_blanks(s, n, k);
        if (m >= n || s[m] != ';' || k - j >= sizeof(out->enum_bases[0].base)) {
            continue;
        }
        CBMTwinCATEnumBase *grown = cbm_realloc(CBM_MEM_CLASS_EXTRACT, out->enum_bases,
                                                (out->enum_base_count + 1) * sizeof(*grown));
        if (!grown) {
            return;
        }
        out->enum_bases = grown;
        CBMTwinCATEnumBase *e = &out->enum_bases[out->enum_base_count++];
        e->st_line = line;
        for (size_t q = 0; q < k - j; q++) {
            e->base[q] = up(s[j + q]);
        }
        e->base[k - j] = '\0';
    }
}

const char *cbm_twincat_enum_base_in(const CBMTwinCATUnit *unit, uint32_t st_first,
                                     uint32_t st_last) {
    for (uint32_t i = 0; unit && i < unit->enum_base_count; i++) {
        uint32_t l = unit->enum_bases[i].st_line;
        if (l >= st_first && l <= st_last) {
            return unit->enum_bases[i].base;
        }
    }
    return NULL;
}

static uint32_t count_lines(const char *s, size_t n) {
    uint32_t lines = 0;
    for (size_t i = 0; i < n; i++) {
        lines += s[i] == '\n';
    }
    if (n > 0 && s[n - 1] != '\n') {
        lines++;
    }
    return lines;
}

bool cbm_twincat_to_st(const char *xml, int xml_len, CBMTwinCATUnit *out) {
    memset(out, 0, sizeof(*out));
    if (!xml || xml_len <= 0) {
        return false;
    }
    size_t n = (size_t)xml_len;
    TcModel m = {0};
    if (!model_parse(&m, xml, n) || m.obj < 0) {
        model_free(&m);
        return false;
    }
    const TcNode *obj = &m.nodes[m.obj];
    const TcPouKind *kind = kind_of(obj->decl.p, obj->decl.len);
    if (!kind) {
        model_free(&m);
        return false;
    }
    TcAsm a = {0};
    assemble(&a, &m, kind);
    model_free(&m);
    if (!a.out.oom) {
        collect_enum_bases(a.out.p ? a.out.p : "", a.out.len, out);
    }
    int norm_len = 0;
    char *norm = (a.out.oom || a.map.oom)
                     ? NULL
                     : cbm_twincat_normalize(a.out.p ? a.out.p : "", (int)a.out.len, &norm_len);
    tb_free(&a.out);
    if (!norm) {
        cbm_free(CBM_MEM_CLASS_EXTRACT, a.map.v);
        cbm_free(CBM_MEM_CLASS_EXTRACT, out->enum_bases);
        memset(out, 0, sizeof(*out));
        return false;
    }
    out->text = norm;

    out->len = norm_len;
    out->xml_line = a.map.v;
    out->line_count = a.map.n;
    out->xml_lines = count_lines(xml, n);
    return true;
}

void cbm_twincat_unit_free(CBMTwinCATUnit *unit) {
    if (!unit) {
        return;
    }
    cbm_free(CBM_MEM_CLASS_EXTRACT, unit->text);
    cbm_free(CBM_MEM_CLASS_EXTRACT, unit->xml_line);
    cbm_free(CBM_MEM_CLASS_EXTRACT, unit->enum_bases);
    memset(unit, 0, sizeof(*unit));
}

uint32_t cbm_twincat_xml_line(const CBMTwinCATUnit *unit, uint32_t st_line) {
    if (!unit || unit->line_count == 0) {
        return st_line;
    }
    if (st_line < 1) {
        st_line = 1;
    }
    if (st_line > unit->line_count) {
        st_line = unit->line_count;
    }
    return unit->xml_line[st_line - 1];
}
