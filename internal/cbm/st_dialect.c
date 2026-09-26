/*
 * st_dialect.c — vendor-dialect normalization for IEC 61131-3 Structured Text.
 *
 * Real .st exports (CODESYS, TwinCAT) use constructs the grammar rejects by
 * design: pragmas, an enum's integer base type, REFERENCE TO, access
 * modifiers on POUs, constructor arguments and array initializers inside
 * declarations, PERSISTENT, AND_THEN/OR_ELSE, hardware address bindings
 * (AT %I*), ARRAY[*], sized STRING[n]/WSTRING[n], and TYPE ... EXTENDS. Each
 * pass is a hand-written scanner rather than a regex: compat_regex is
 * POSIX-only and has neither lookahead nor a portable \b. Every pass
 * reproduces its reference pattern's match semantics, including case
 * sensitivity (constructor arguments and ARRAY ... OF are matched
 * case-sensitively on purpose) and word boundaries, where bytes >= 0x80
 * count as word characters (UTF-8 letters). The keyword rewrites (UNION,
 * REFERENCE TO, AND_THEN/OR_ELSE, AT %I*, an enum base) do not skip comments
 * or strings: a rewrite there changes no definition, call or usage.
 *
 * Declaration-level passes (array initializers, constructor arguments, a
 * doubled ';') run only inside VAR ... END_VAR and STRUCT ... END_STRUCT
 * regions, where statements cannot live: applied to the whole file they
 * turned invalid statement code into a clean parse.
 *
 * Every pass preserves the number and order of newlines — deleted text gives
 * back the newlines it contained — so line N of the normalized source is
 * still line N of the original file, and definitions are reported at their
 * real position without any remap.
 */
#include "st_dialect.h"

#include "foundation/constants.h"
#include "foundation/mem_core.h" // per-file transient: freed inside one extraction call

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

enum {
    ST_BUF_INIT = 4096,
    ST_BUF_GROWTH = 2,
    ST_UTF8_BYTE = 0x80,
};

/* Length of a string literal without its NUL. */
#define ST_LIT_LEN(lit) (sizeof(lit) - SKIP_ONE)

/* ── growable byte buffer ─────────────────────────────────────────────────── */

typedef struct {
    char *p;
    size_t len;
    size_t cap;
    bool oom;
} StBuf;

static void tb_reserve(StBuf *b, size_t extra) {
    if (b->oom) {
        return;
    }
    size_t need = b->len + extra + SKIP_ONE; /* the NUL */
    if (b->p && need <= b->cap) {
        return;
    }
    size_t cap = b->cap ? b->cap : ST_BUF_INIT;
    while (cap < need) {
        cap *= ST_BUF_GROWTH;
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

static void tb_put(StBuf *b, const char *s, size_t n) {
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

static void tb_putc(StBuf *b, char c) {
    tb_put(b, &c, SKIP_ONE);
}

static void tb_free(StBuf *b) {
    cbm_free(CBM_MEM_CLASS_EXTRACT, b->p);
    memset(b, 0, sizeof(*b));
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
    return is_alpha_(c) || is_digit(c) || (unsigned char)c >= ST_UTF8_BYTE;
}

static char up(char c) {
    if (c >= 'a' && c <= 'z') {
        return (char)(c - ('a' - 'A'));
    }
    return c;
}

/* s[i] or NUL past the end. */
static char at_or_nul(const char *s, size_t n, size_t i) {
    if (i < n) {
        return s[i];
    }
    return '\0';
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
    return i == 0 || !is_word(s[i - SKIP_ONE]);
}

/* \b after a word character ending at j. */
static bool ends_word(const char *s, size_t n, size_t j) {
    return j >= n || !is_word(s[j]);
}

/* Whole word `kw` (case-insensitive) at s[i]. */
static bool word_at(const char *s, size_t n, size_t i, const char *kw) {
    return starts_word(s, i) && ci_at(s, n, i, kw) && ends_word(s, n, i + strlen(kw));
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

/* End of the line that starts at i (the '\n' or n). */
static size_t line_end(const char *s, size_t n, size_t i) {
    while (i < n && s[i] != '\n') {
        i++;
    }
    return i;
}

/* Start of the line after the one ending at eol. */
static size_t line_next(size_t n, size_t eol) {
    return eol < n ? eol + SKIP_ONE : n;
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

/* Terminator of the block comment or pragma that opens with c d, or NULL. */
static const char *block_closer(char c, char d) {
    if (c == '(' && d == '*') {
        return "*)";
    }
    if (c == '/' && d == '*') {
        return "*/";
    }
    return c == '{' ? "}" : NULL;
}

/* Start of the first `seq` at or after from, or n. */
static size_t find_seq(const char *s, size_t n, size_t from, const char *seq) {
    size_t sl = strlen(seq);
    for (size_t j = from; j < n; j++) {
        if (n - j >= sl && memcmp(s + j, seq, sl) == 0) {
            return j;
        }
    }
    return n;
}

/* Position after the first `close` at or after from, or n. */
static size_t skip_past(const char *s, size_t n, size_t from, const char *close) {
    size_t j = find_seq(s, n, from, close);
    return j < n ? j + strlen(close) : n;
}

/* End of the '...' or "..." literal opening at s[i] ($ escapes the next
 * byte); stops at a newline so a stray quote cannot swallow the file. */
static size_t string_end(const char *s, size_t n, size_t i) {
    char q = s[i];
    size_t j = i + SKIP_ONE;
    while (j < n && s[j] != '\n') {
        if (s[j] == '$' && j + SKIP_ONE < n && s[j + SKIP_ONE] != '\n') {
            j += PAIR_LEN;
            continue;
        }
        if (s[j++] == q) {
            break;
        }
    }
    return j;
}

/* End of the comment, string or {pragma} that starts at s[i], or i when none
 * starts there. Tokenizes like st_unit: (* *) does not nest, a string stops at
 * a newline so a stray quote cannot swallow the rest of the file. */
static size_t trivia_end(const char *s, size_t n, size_t i) {
    char c = s[i];
    char d = at_or_nul(s, n, i + SKIP_ONE);
    const char *close = block_closer(c, d);
    if (close) {
        return skip_past(s, n, i + SKIP_ONE, close);
    }
    if (c == '/' && d == '/') {
        return line_end(s, n, i);
    }
    if (c == '\'' || c == '"') {
        return string_end(s, n, i);
    }
    return i;
}

/* Skip whitespace (newlines included), comments and pragmas. */
static size_t skip_space_comments(const char *s, size_t n, size_t i) {
    for (;;) {
        while (i < n && is_space(s[i])) {
            i++;
        }
        size_t t = (i < n && s[i] != '\'' && s[i] != '"') ? trivia_end(s, n, i) : i;
        if (t == i) {
            return i;
        }
        i = t;
    }
}

/* Every section keyword a declaration block opens with (VAR_STAT and
 * VAR_INST are vendor sections pass_var_stat maps to VAR). */
static const char *const VAR_SECTIONS[] = {"VAR",        "VAR_INPUT",  "VAR_OUTPUT", "VAR_IN_OUT",
                                           "VAR_TEMP",   "VAR_STAT",   "VAR_INST",   "VAR_EXTERNAL",
                                           "VAR_GLOBAL", "VAR_CONFIG", "VAR_ACCESS", NULL};

/* ── copy-with-replacements cursor ────────────────────────────────────────── */

typedef struct {
    StBuf *out;
    const char *s;
    size_t from; /* first input byte not yet copied */
} StCopy;

static void cp_flush(StCopy *c, size_t upto) {
    if (upto > c->from) {
        tb_put(c->out, c->s + c->from, upto - c->from);
        c->from = upto;
    }
}

/* Replace s[start, end) with rep, giving back every newline the span held. */
static void cp_replace(StCopy *c, size_t start, size_t end, const char *rep, size_t rep_len) {
    cp_flush(c, start);
    tb_put(c->out, rep, rep_len);
    for (size_t q = start; q < end; q++) {
        if (c->s[q] == '\n') {
            tb_putc(c->out, '\n');
        }
    }
    c->from = end;
}

/* Replace s[start, end) with as many blanks (same length, same line). */
static void cp_blank(StCopy *c, size_t start, size_t end) {
    cp_flush(c, start);
    for (size_t q = start; q < end; q++) {
        tb_putc(c->out, ' ');
    }
    c->from = end;
}

typedef void (*StPass)(StBuf *out, const char *s, size_t n);

/* ── normalization passes ─────────────────────────────────────────────────── */

/* True when s[from, to) holds "(*" or "*)". */
static bool has_comment_delim(const char *s, size_t from, size_t to) {
    for (size_t q = from; q + SKIP_ONE < to; q++) {
        if ((s[q] == '(' && s[q + SKIP_ONE] == '*') || (s[q] == '*' && s[q + SKIP_ONE] == ')')) {
            return true;
        }
    }
    return false;
}

/* True when the line s[i, eol) holds only one {pragma} (and blanks, a CR). */
static bool pragma_only_line(const char *s, size_t eol, size_t i) {
    size_t j = skip_blanks(s, eol, i);
    if (j >= eol || s[j] != '{') {
        return false;
    }
    size_t k = j + SKIP_ONE;
    while (k < eol && s[k] != '}') {
        k++;
    }
    if (k >= eol || has_comment_delim(s, j + SKIP_ONE, k)) {
        return false;
    }
    size_t m = skip_blanks(s, eol, k + SKIP_ONE);
    if (m < eol && s[m] == '\r') {
        m++;
    }
    return m == eol;
}

/* A line holding only a {pragma}, but never one carrying a comment delimiter:
 * "{*) x (*}" closes and reopens a block comment, so dropping it would turn
 * dead code live. The line is blanked, not removed. */
static void pass_pragma(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t eol = line_end(s, n, i);
        if (eol < n && pragma_only_line(s, eol, i)) {
            cp_replace(&c, i, eol, "", 0);
        }
        i = line_next(n, eol);
    }
    cp_flush(&c, n);
}

/* Integer base types an enum may carry: "TYPE E : ( ... ) UINT;". */
static const char *const ENUM_BASES[] = {"UINT", "INT",   "BYTE",  "WORD", "DWORD", "DINT",
                                         "SINT", "USINT", "UDINT", "LINT", "ULINT", NULL};

/* "UNION" / "END_UNION" -> "STRUCT" / "END_STRUCT": the grammar has no union,
 * and for the graph a union's members are fields of the type like a struct's. */
static void pass_union(StBuf *out, const char *s, size_t n) {
    static const char END_UNION[] = "END_UNION";
    static const char UNION[] = "UNION";
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'E' && word_at(s, n, i, END_UNION)) {
            cp_replace(&c, i, i + ST_LIT_LEN(END_UNION), "END_STRUCT", ST_LIT_LEN("END_STRUCT"));
            i += ST_LIT_LEN(END_UNION);
            continue;
        }
        if (up(s[i]) == 'U' && word_at(s, n, i, UNION)) {
            cp_replace(&c, i, i + ST_LIT_LEN(UNION), "STRUCT", ST_LIT_LEN("STRUCT"));
            i += ST_LIT_LEN(UNION);
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* END_STRUCT not followed by ';' gets one. */
static void pass_struct_semi(StBuf *out, const char *s, size_t n) {
    static const char KW[] = "END_STRUCT";
    static const char KW_SEMI[] = "END_STRUCT;";
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t t = trivia_end(s, n, i);
        if (t > i) {
            i = t;
            continue;
        }
        if (up(s[i]) == 'E' && word_at(s, n, i, KW)) {
            size_t j = i + ST_LIT_LEN(KW);
            while (j < n && is_space(s[j])) {
                j++;
            }
            if (j >= n || s[j] != ';') {
                cp_replace(&c, i, i + ST_LIT_LEN(KW), KW_SEMI, ST_LIT_LEN(KW_SEMI));
            }
            i += ST_LIT_LEN(KW);
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* "STRUCT END_STRUCT" -> "STRUCT _ : BOOL; END_STRUCT": the grammar needs at
 * least one field, exports carry empty ones (a derived DUT that adds no
 * field). Struct fields become no graph node, so the placeholder stays
 * invisible while the type itself is kept. */
static void pass_empty_struct(StBuf *out, const char *s, size_t n) {
    static const char FIELD[] = " _ : BOOL;";
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t t = trivia_end(s, n, i);
        if (t > i) {
            i = t;
            continue;
        }
        if (up(s[i]) == 'S' && word_at(s, n, i, "STRUCT")) {
            size_t e = i + ST_LIT_LEN("STRUCT");
            size_t j = skip_space_comments(s, n, e);
            if (ci_at(s, n, j, "END_STRUCT") && ends_word(s, n, j + ST_LIT_LEN("END_STRUCT"))) {
                cp_replace(&c, e, e, FIELD, ST_LIT_LEN(FIELD));
            }
            i = e;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* Enum base type ") UINT;" -> ");". */
static void pass_enum_base(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n; i++) {
        if (s[i] != ')') {
            continue;
        }
        size_t j = skip_blanks(s, n, i + SKIP_ONE);
        size_t k = word_end(s, n, j);
        if (k > j && span_in(s + j, k - j, ENUM_BASES)) {
            size_t m = skip_blanks(s, n, k);
            if (m < n && s[m] == ';') {
                cp_replace(&c, i, m + SKIP_ONE, ");", ST_LIT_LEN(");"));
                i = m;
            }
        }
    }
    cp_flush(&c, n);
}

/* End of the "%I*" / "%QX0.1" address that follows "AT" + blanks at s[j], or 0. */
static size_t address_end(const char *s, size_t n, size_t j) {
    if (!j || j + SKIP_ONE >= n || s[j] != '%') {
        return 0;
    }
    char area = up(s[j + SKIP_ONE]);
    if (area != 'I' && area != 'Q' && area != 'M') {
        return 0;
    }
    size_t k = j + PAIR_LEN;
    while (k < n && (is_alpha_(s[k]) || is_digit(s[k]) || s[k] == '.' || s[k] == '*') &&
           s[k] != '_') {
        k++;
    }
    return k;
}

/* "AT %I*" / "AT %QX0.1" hardware address bindings are dropped. */
static void pass_at_address(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'A' && starts_word(s, i) && ci_at(s, n, i, "AT")) {
            size_t k = address_end(s, n, need_blanks(s, n, i + ST_LIT_LEN("AT")));
            if (k) {
                cp_replace(&c, i, k, "", 0);
                i = k;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

static void pass_reference_to(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'R' && starts_word(s, i) && ci_at(s, n, i, "REFERENCE")) {
            size_t j = need_blanks(s, n, i + ST_LIT_LEN("REFERENCE"));
            if (j && ci_at(s, n, j, "TO") && ends_word(s, n, j + ST_LIT_LEN("TO"))) {
                size_t end = j + ST_LIT_LEN("TO");
                cp_replace(&c, i, end, "POINTER TO", ST_LIT_LEN("POINTER TO"));
                i = end;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

static void pass_var_stat(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'V' && starts_word(s, i) &&
            (ci_at(s, n, i, "VAR_STAT") || ci_at(s, n, i, "VAR_INST")) &&
            ends_word(s, n, i + ST_LIT_LEN("VAR_STAT"))) {
            size_t e = i + ST_LIT_LEN("VAR_STAT");
            cp_replace(&c, i, e, "VAR", ST_LIT_LEN("VAR"));
            i = e;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* End of "[RETAIN] PERSISTENT" after the section keyword ending at k, or 0. */
static size_t persistent_end(const char *s, size_t n, size_t k) {
    size_t j = need_blanks(s, n, k);
    if (!j) {
        return 0;
    }
    size_t r = ci_at(s, n, j, "RETAIN") ? need_blanks(s, n, j + ST_LIT_LEN("RETAIN")) : 0;
    if (r && ci_at(s, n, r, "PERSISTENT") && ends_word(s, n, r + ST_LIT_LEN("PERSISTENT"))) {
        return r + ST_LIT_LEN("PERSISTENT");
    }
    if (ci_at(s, n, j, "PERSISTENT") && ends_word(s, n, j + ST_LIT_LEN("PERSISTENT"))) {
        return j + ST_LIT_LEN("PERSISTENT");
    }
    return 0;
}

/* "VAR [RETAIN] PERSISTENT" keeps the section keyword only. */
static void pass_persistent(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) != 'V' || !starts_word(s, i) || !ci_at(s, n, i, "VAR")) {
            i++;
            continue;
        }
        size_t k = word_end(s, n, i);
        size_t end = span_in(s + i, k - i, VAR_SECTIONS) ? persistent_end(s, n, k) : 0;
        if (end) {
            cp_replace(&c, k, end, "", 0);
            i = end;
        } else {
            i = k;
        }
    }
    cp_flush(&c, n);
}

static void pass_and_then(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (word_at(s, n, i, "AND_THEN")) {
            cp_replace(&c, i, i + ST_LIT_LEN("AND_THEN"), "AND", ST_LIT_LEN("AND"));
            i += ST_LIT_LEN("AND_THEN");
            continue;
        }
        if (word_at(s, n, i, "OR_ELSE")) {
            cp_replace(&c, i, i + ST_LIT_LEN("OR_ELSE"), "OR", ST_LIT_LEN("OR"));
            i += ST_LIT_LEN("OR_ELSE");
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* ── declaration regions: VAR ... END_VAR and STRUCT ... END_STRUCT ───────── */

/* Terminator of the block comment or pragma opening at s[p] (strings and //
 * comments excluded), with its opener length in *skip, or NULL. */
static const char *code_trivia_opens(const char *s, size_t eol, size_t p, size_t *skip) {
    char c = s[p];
    char d = at_or_nul(s, eol, p + SKIP_ONE);
    const char *close = block_closer(c, d);
    *skip = close && c == '{' ? SKIP_ONE : PAIR_LEN;
    return close;
}

/* Scan s[p, eol) as code. `*open` is the terminator of a block comment or
 * pragma still open from an earlier line (NULL when none) and is left as it
 * stands at eol. Returns the first whole word `kw` found in code, or eol
 * (always eol when kw is NULL). Strings and // comments are skipped. */
static size_t line_find_word(const char *s, size_t eol, size_t p, const char **open,
                             const char *kw) {
    while (p < eol) {
        if (*open) {
            size_t e = find_seq(s, eol, p, *open);
            if (e >= eol) {
                return eol;
            }
            p = e + strlen(*open);
            *open = NULL;
            continue;
        }
        size_t skip = 0;
        const char *close = code_trivia_opens(s, eol, p, &skip);
        if (close) {
            *open = close;
            p += skip;
        } else if (s[p] == '/' && at_or_nul(s, eol, p + SKIP_ONE) == '/') {
            return eol;
        } else if (s[p] == '\'' || s[p] == '"') {
            p = string_end(s, eol, p);
        } else if (kw && word_at(s, eol, p, kw)) {
            return p;
        } else {
            p++;
        }
    }
    return eol;
}

/* End of a VAR section keyword opening the line, or 0. */
static size_t line_opens_var(const char *s, size_t eol, size_t i) {
    size_t j = skip_blanks(s, eol, i);
    if (!ci_at(s, eol, j, "VAR")) {
        return 0;
    }
    size_t k = word_end(s, eol, j);
    return span_in(s + j, k - j, VAR_SECTIONS) ? k : 0;
}

/* End of STRUCT as the line's first word or in the code of a "TYPE X :"
 * header line, or 0. */
static size_t line_opens_struct(const char *s, size_t eol, size_t i) {
    size_t j = skip_blanks(s, eol, i);
    if (ci_at(s, eol, j, "STRUCT") && ends_word(s, eol, j + ST_LIT_LEN("STRUCT"))) {
        return j + ST_LIT_LEN("STRUCT");
    }
    if (!ci_at(s, eol, j, "TYPE") || !ends_word(s, eol, j + ST_LIT_LEN("TYPE"))) {
        return 0;
    }
    const char *open = NULL;
    size_t k = line_find_word(s, eol, j + ST_LIT_LEN("TYPE"), &open, "STRUCT");
    return k < eol ? k + ST_LIT_LEN("STRUCT") : 0;
}

/* Closer of the declaration region the code line s[i, eol) opens, with the
 * end of its opening keyword in *body, or NULL. */
static const char *line_opens_region(const char *s, size_t eol, size_t i, size_t *body) {
    *body = line_opens_var(s, eol, i);
    if (*body) {
        return "END_VAR";
    }
    *body = line_opens_struct(s, eol, i);
    return *body ? "END_STRUCT" : NULL;
}

/* Apply `fn` to every VAR ... END_VAR and STRUCT ... END_STRUCT region (open
 * and close lines included); copy everything else unchanged. Both hold only
 * declarations. A region opens only on a line that starts in code, and ends
 * on the first line whose code holds its closer, wherever on that line (the
 * opening line included), so no region runs into the code after its block.
 * An unterminated region runs to the end. */
static void in_decl_blocks(StBuf *out, const char *s, size_t n, StPass fn) {
    const char *closer = NULL;
    const char *open = NULL; /* block comment / pragma open at the line start */
    size_t region = 0;
    for (size_t i = 0; i < n;) {
        size_t eol = line_end(s, n, i);
        size_t next = line_next(n, eol);
        const char *line_open = open;
        (void)line_find_word(s, eol, i, &open, NULL);
        size_t from = i;
        if (!closer) {
            closer = line_open ? NULL : line_opens_region(s, eol, i, &from);
            if (!closer) {
                tb_put(out, s + i, next - i);
                i = next;
                continue;
            }
            region = i;
        }
        if (line_find_word(s, eol, from, &line_open, closer) < eol) {
            fn(out, s + region, next - region);
            closer = NULL;
        }
        i = next;
    }
    if (closer) {
        fn(out, s + region, n - region);
    }
}

/* ":= [ ... ]" array initializer before ';' is dropped. */
static void region_arr_init(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i + SKIP_ONE < n; i++) {
        if (s[i] != ':' || s[i + SKIP_ONE] != '=') {
            continue;
        }
        size_t j = i + PAIR_LEN;
        while (j < n && is_space(s[j]) && s[j] != '\f' && s[j] != '\v') {
            j++;
        }
        if (j >= n || s[j] != '[') {
            continue;
        }
        size_t k = j + SKIP_ONE;
        while (k < n && s[k] != ']') {
            k++;
        }
        if (k >= n) {
            continue;
        }
        size_t m = skip_blanks(s, n, k + SKIP_ONE);
        if (m < n && s[m] == ';') {
            cp_replace(&c, i, m, "", 0);
            i = m - SKIP_ONE;
        }
    }
    cp_flush(&c, n);
}

/* Position after "ARRAY [..] OF" plus blanks at s[p] (case-sensitive, as in
 * the reference pattern), or p when there is none. */
static size_t skip_array_of(const char *s, size_t n, size_t p) {
    if (!cs_at(s, n, p, "ARRAY")) {
        return p;
    }
    size_t q = skip_blanks(s, n, p + ST_LIT_LEN("ARRAY"));
    if (q >= n || s[q] != '[') {
        return p;
    }
    q++;
    while (q < n && s[q] != ']' && s[q] != '\n') {
        q++;
    }
    if (q >= n || s[q] != ']') {
        return p;
    }
    q = skip_blanks(s, n, q + SKIP_ONE);
    return cs_at(s, n, q, "OF") ? skip_blanks(s, n, q + ST_LIT_LEN("OF")) : p;
}

/* End of the type name in "name : [ARRAY[..] OF] Type" at the line start i,
 * or 0. */
static size_t ctor_type_end(const char *s, size_t n, size_t i) {
    size_t p = skip_blanks(s, n, i);
    if (p >= n || !is_alpha_(s[p])) {
        return 0;
    }
    p = skip_blanks(s, n, word_end(s, n, p + SKIP_ONE));
    if (p >= n || s[p] != ':') {
        return 0;
    }
    p = skip_array_of(s, n, skip_blanks(s, n, p + SKIP_ONE));
    if (p >= n || !is_alpha_(s[p])) {
        return 0;
    }
    p++;
    while (p < n && (is_word(s[p]) || s[p] == '.')) {
        p++;
    }
    return p;
}

/* Index of the ')' closing the argument list opening at s[p] (one level of
 * nested parentheses), or 0. */
static size_t ctor_args_close(const char *s, size_t n, size_t p) {
    for (size_t q = p + SKIP_ONE; q < n; q++) {
        if (s[q] == ')') {
            return q;
        }
        if (s[q] == '(') {
            size_t r = q + SKIP_ONE;
            while (r < n && s[r] != '(' && s[r] != ')') {
                r++;
            }
            if (r >= n || s[r] != ')') {
                return 0;
            }
            q = r;
        }
    }
    return 0;
}

/* Constructor arguments at a line start: "name : [ARRAY[..] OF] Type(args);"
 * -> "name : [ARRAY[..] OF] Type;". One level of nested parentheses, args may
 * span lines. ARRAY/OF are case-sensitive, as in the reference pattern.
 * Returns the index after ';' or 0; g1_end = end of the kept head,
 * g2_start = first byte after ')'. */
static size_t ctor_match(const char *s, size_t n, size_t i, size_t *g1_end, size_t *g2_start) {
    size_t p = ctor_type_end(s, n, i);
    if (!p) {
        return 0;
    }
    *g1_end = p;
    p = skip_blanks(s, n, p);
    if (p >= n || s[p] != '(') {
        return 0;
    }
    size_t q = ctor_args_close(s, n, p);
    if (!q) {
        return 0;
    }
    *g2_start = q + SKIP_ONE;
    size_t m = skip_blanks(s, n, q + SKIP_ONE);
    if (m >= n || s[m] != ';') {
        return 0;
    }
    return m + SKIP_ONE;
}

static void region_ctor_args(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
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
        i = line_next(n, line_end(s, n, resume));
    }
    cp_flush(&c, n);
}

/* "x : BOOL;;" -> "x : BOOL; ": an empty declaration is an ERROR, while in a
 * body the grammar takes ";;" as an empty statement, hence the region scope. */
static void region_double_semi(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t t = trivia_end(s, n, i);
        if (t > i) {
            i = t;
            continue;
        }
        if (s[i] == ';') {
            size_t j = skip_blanks(s, n, i + SKIP_ONE);
            if (j < n && s[j] == ';') {
                cp_replace(&c, j, j + SKIP_ONE, " ", SKIP_ONE);
                i = j; /* the blanked ';' may be followed by another */
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

static void pass_arr_init(StBuf *out, const char *s, size_t n) {
    in_decl_blocks(out, s, n, region_arr_init);
}

static void pass_ctor_args(StBuf *out, const char *s, size_t n) {
    in_decl_blocks(out, s, n, region_ctor_args);
}

static void pass_double_semi(StBuf *out, const char *s, size_t n) {
    in_decl_blocks(out, s, n, region_double_semi);
}

/* ── remaining passes ─────────────────────────────────────────────────────── */

/* End of "[*]" (blanks allowed) after ARRAY ending at i, or 0. */
static size_t star_dims_end(const char *s, size_t n, size_t i) {
    size_t j = skip_blanks(s, n, i);
    if (j >= n || s[j] != '[') {
        return 0;
    }
    j = skip_blanks(s, n, j + SKIP_ONE);
    if (j >= n || s[j] != '*') {
        return 0;
    }
    j = skip_blanks(s, n, j + SKIP_ONE);
    return (j < n && s[j] == ']') ? j + SKIP_ONE : 0;
}

static void pass_array_star(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'A' && starts_word(s, i) && ci_at(s, n, i, "ARRAY")) {
            size_t end = star_dims_end(s, n, i + ST_LIT_LEN("ARRAY"));
            if (end) {
                cp_replace(&c, i, end, "ARRAY[1..1]", ST_LIT_LEN("ARRAY[1..1]"));
                i = end;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* Length of STRING / WSTRING starting a word at s[i], or 0. */
static size_t string_kw_at(const char *s, size_t n, size_t i) {
    if (!starts_word(s, i)) {
        return 0;
    }
    if (up(s[i]) == 'W' && ci_at(s, n, i + SKIP_ONE, "STRING")) {
        return ST_LIT_LEN("WSTRING");
    }
    return ci_at(s, n, i, "STRING") ? ST_LIT_LEN("STRING") : 0;
}

/* STRING[80] / WSTRING[80] -> STRING / WSTRING (keeps the original spelling). */
static void pass_str_len(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t g = string_kw_at(s, n, i);
        size_t j = g ? skip_blanks(s, n, i + g) : n;
        if (j < n && s[j] == '[') {
            size_t k = j + SKIP_ONE;
            while (k < n && s[k] != ']' && s[k] != '\n') {
                k++;
            }
            if (k < n && s[k] == ']') {
                cp_flush(&c, i + g);
                c.from = k + SKIP_ONE;
                i = k + SKIP_ONE;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* "FUNCTION_BLOCK PUBLIC X" / "PROGRAM INTERNAL X" -> keyword + one space + X. */
static void pass_pou_access(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t kl = 0;
        if (starts_word(s, i)) {
            if (ci_at(s, n, i, "PROGRAM")) {
                kl = ST_LIT_LEN("PROGRAM");
            } else if (ci_at(s, n, i, "FUNCTION_BLOCK")) {
                kl = ST_LIT_LEN("FUNCTION_BLOCK");
            }
        }
        size_t j = kl ? need_blanks(s, n, i + kl) : 0;
        size_t ml = j ? modifier_at(s, n, j) : 0;
        size_t m = ml ? need_blanks(s, n, j + ml) : 0;
        if (m && m < n && is_alpha_(s[m])) {
            cp_replace(&c, i + kl, m, " ", SKIP_ONE);
            i = m;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

/* True when the line s[i, eol) starts with the whole word `kw`. */
static bool line_starts_with(const char *s, size_t eol, size_t i, const char *kw) {
    size_t j = skip_blanks(s, eol, i);
    return ci_at(s, eol, j, kw) && ends_word(s, eol, j + strlen(kw));
}

/* True when the line s[i, eol) starts with a POU keyword and a name. */
static bool line_starts_pou(const char *s, size_t eol, size_t i) {
    static const char *const POUS[] = {"FUNCTION_BLOCK", "FUNCTION", "PROGRAM",
                                       "INTERFACE",      "TYPE",     NULL};
    size_t j = skip_blanks(s, eol, i);
    size_t k = word_end(s, eol, j);
    if (k == j || !span_in(s + j, k - j, POUS)) {
        return false;
    }
    size_t m = need_blanks(s, eol, k);
    return m && m < eol && is_alpha_(s[m]);
}

/* Name start of a "PROGRAM <name>" header opening the line s[i, eol), with
 * the keyword's start in *kw, or 0. */
static size_t line_program_name(const char *s, size_t eol, size_t i, size_t *kw) {
    size_t j = skip_blanks(s, eol, i);
    if (!ci_at(s, eol, j, "PROGRAM") || !ends_word(s, eol, j + ST_LIT_LEN("PROGRAM"))) {
        return 0;
    }
    size_t k = need_blanks(s, eol, j + ST_LIT_LEN("PROGRAM"));
    if (!k || k >= eol || !is_alpha_(s[k])) {
        return 0;
    }
    *kw = j;
    return k;
}

typedef struct {
    bool has_member; /* a METHOD or PROPERTY line in code belongs to it */
    size_t end_kw;   /* offset of its END_PROGRAM, or n when it has none */
} StProgram;

/* Scan the PROGRAM whose body starts at `from` (`open` = the comment state
 * there) up to the header of the next POU: the members exported after its
 * END_PROGRAM belong to it as well. */
static StProgram program_extent(const char *s, size_t n, size_t from, const char *open) {
    StProgram p = {false, n};
    for (size_t i = from; i < n;) {
        size_t eol = line_end(s, n, i);
        const char *line_open = open;
        (void)line_find_word(s, eol, i, &open, NULL);
        if (!line_open && line_starts_pou(s, eol, i)) {
            break;
        }
        if (!line_open &&
            (line_starts_with(s, eol, i, "METHOD") || line_starts_with(s, eol, i, "PROPERTY"))) {
            p.has_member = true;
        }
        if (p.end_kw == n) {
            size_t e = line_find_word(s, eol, i, &line_open, "END_PROGRAM");
            p.end_kw = e < eol ? e : n;
        }
        i = line_next(n, eol);
    }
    return p;
}

/* A PROGRAM that owns METHODs or PROPERTYs is only valid as a FUNCTION_BLOCK:
 * its header and its END_PROGRAM are rewritten together, one PROGRAM at a
 * time, so every other PROGRAM in the file keeps both. */
static void pass_program_as_fb(StBuf *out, const char *s, size_t n) {
    static const char FB[] = "FUNCTION_BLOCK ";
    static const char END_FB[] = "END_FUNCTION_BLOCK";
    StCopy c = {out, s, 0};
    const char *open = NULL;
    for (size_t i = 0; i < n;) {
        size_t eol = line_end(s, n, i);
        size_t next = line_next(n, eol);
        const char *line_open = open;
        (void)line_find_word(s, eol, i, &open, NULL);
        size_t kw = 0;
        size_t name = line_open ? 0 : line_program_name(s, eol, i, &kw);
        StProgram p = name ? program_extent(s, n, next, open) : (StProgram){false, n};
        if (p.has_member) {
            cp_replace(&c, kw, name, FB, ST_LIT_LEN(FB));
            if (p.end_kw < n) {
                cp_replace(&c, p.end_kw, p.end_kw + ST_LIT_LEN("END_PROGRAM"), END_FB,
                           ST_LIT_LEN(END_FB));
            }
        }
        i = next;
    }
    cp_flush(&c, n);
}

/* Position after any access modifiers (each followed by a blank) after p. */
static size_t skip_modifiers(const char *s, size_t n, size_t p) {
    for (;;) {
        size_t q = need_blanks(s, n, p);
        size_t ml = q ? modifier_at(s, n, q) : 0;
        if (!ml || q + ml >= n || !is_blank(s[q + ml])) {
            return p;
        }
        p = q + ml;
    }
}

/* End of " ABSTRACT" / " FINAL" at p, or 0. */
static size_t abstract_final_end(const char *s, size_t n, size_t p) {
    size_t q = need_blanks(s, n, p);
    if (q && ci_at(s, n, q, "ABSTRACT") && ends_word(s, n, q + ST_LIT_LEN("ABSTRACT"))) {
        return q + ST_LIT_LEN("ABSTRACT");
    }
    if (q && ci_at(s, n, q, "FINAL") && ends_word(s, n, q + ST_LIT_LEN("FINAL"))) {
        return q + ST_LIT_LEN("FINAL");
    }
    return 0;
}

/* ABSTRACT / FINAL after FUNCTION_BLOCK, METHOD or PROPERTY (and any access
 * modifiers) are dropped. */
static void pass_modifier(StBuf *out, const char *s, size_t n) {
    static const char *const KWS[] = {"FUNCTION_BLOCK", "METHOD", "PROPERTY", NULL};
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t kl = 0;
        for (size_t k = 0; KWS[k] && !kl && starts_word(s, i); k++) {
            kl = ci_at(s, n, i, KWS[k]) ? strlen(KWS[k]) : 0;
        }
        if (!kl) {
            i++;
            continue;
        }
        size_t p = skip_modifiers(s, n, i + kl);
        size_t end = abstract_final_end(s, n, p);
        if (end) {
            cp_replace(&c, p, end, "", 0);
            i = end;
        } else {
            i += kl;
        }
    }
    cp_flush(&c, n);
}

/* End of " EXTENDS Base" after the type name ending at k, or 0. */
static size_t type_extends_end(const char *s, size_t n, size_t k) {
    size_t m = need_blanks(s, n, k);
    size_t b = (m && ci_at(s, n, m, "EXTENDS")) ? need_blanks(s, n, m + ST_LIT_LEN("EXTENDS")) : 0;
    if (!b || b >= n || !is_alpha_(s[b])) {
        return 0;
    }
    size_t e = b + SKIP_ONE;
    while (e < n && (is_word(s[e]) || s[e] == '.')) {
        e++;
    }
    return e;
}

/* "TYPE T_X EXTENDS T_Base :" -> "TYPE T_X :". */
static void pass_type_extends(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        if (up(s[i]) == 'T' && starts_word(s, i) && ci_at(s, n, i, "TYPE")) {
            size_t j = need_blanks(s, n, i + ST_LIT_LEN("TYPE"));
            size_t k = (j && j < n && is_alpha_(s[j])) ? word_end(s, n, j + SKIP_ONE) : 0;
            size_t e = k ? type_extends_end(s, n, k) : 0;
            if (e) {
                cp_replace(&c, k, e, "", 0);
                i = e;
                continue;
            }
        }
        i++;
    }
    cp_flush(&c, n);
}

/* True when the '.' at s[i] follows an operand that can carry a bit index:
 * an identifier (not a number, not the tail of a 16#FF or %IX0 literal) or a
 * closing ']'. */
static bool bit_access_owner(const char *s, size_t i) {
    if (i == 0) {
        return false;
    }
    char prev = s[i - SKIP_ONE];
    if (prev == ']') {
        return true;
    }
    if (!is_word(prev)) {
        return false;
    }
    size_t k = i - SKIP_ONE;
    while (k > 0 && is_word(s[k - SKIP_ONE])) {
        k--;
    }
    if (is_digit(s[k])) {
        return false;
    }
    return k == 0 || (s[k - SKIP_ONE] != '#' && s[k - SKIP_ONE] != '%');
}

/* End of the ".N" bit index at s[i], or 0. */
static size_t bit_index_end(const char *s, size_t n, size_t i) {
    if (s[i] != '.' || !is_digit(at_or_nul(s, n, i + SKIP_ONE)) || !bit_access_owner(s, i)) {
        return 0;
    }
    size_t j = i + SKIP_ONE;
    while (j < n && is_digit(s[j])) {
        j++;
    }
    return (ends_word(s, n, j) && (j >= n || s[j] != '.')) ? j : 0;
}

/* Bit access "x.3" / "a[1].0" / "s.Flags.7" -> the ".N" becomes blanks: the
 * grammar has no integer bit index, and the variable stays a read or write
 * of itself, which is what the access means for the graph. */
static void pass_bit_access(StBuf *out, const char *s, size_t n) {
    StCopy c = {out, s, 0};
    for (size_t i = 0; i < n;) {
        size_t t = trivia_end(s, n, i);
        if (t > i) {
            i = t;
            continue;
        }
        size_t j = bit_index_end(s, n, i);
        if (j) {
            cp_blank(&c, i, j);
            i = j;
            continue;
        }
        i++;
    }
    cp_flush(&c, n);
}

char *cbm_st_normalize(const char *src, int len, int *out_len) {
    static const StPass PASSES[] = {
        pass_pragma,     pass_union,         pass_struct_semi, pass_empty_struct, pass_enum_base,
        pass_at_address, pass_reference_to,  pass_var_stat,    pass_persistent,   pass_and_then,
        pass_arr_init,   pass_ctor_args,     pass_double_semi, pass_array_star,   pass_str_len,
        pass_pou_access, pass_program_as_fb, pass_modifier,    pass_type_extends, pass_bit_access,
    };
    StBuf cur = {0};
    tb_put(&cur, src ? src : "", (src && len > 0) ? (size_t)len : 0);
    for (size_t k = 0; k < sizeof(PASSES) / sizeof(PASSES[0]) && !cur.oom; k++) {
        StBuf next = {0};
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
