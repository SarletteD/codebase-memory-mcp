#ifndef CBM_ST_UNIT_H
#define CBM_ST_UNIT_H

/*
 * Parser text for one IEC 61131-3 Structured Text (.st) source.
 *
 * CODESYS/TwinCAT exports write a FUNCTION_BLOCK's METHOD and PROPERTY
 * members AFTER its END_FUNCTION_BLOCK (and an INTERFACE's after its
 * END_INTERFACE), while the grammar accepts members only inside the
 * container, after its VAR blocks and before its body statements. The unit
 * moves those trailing members back to that position and records, for every
 * line of the parser text, the line of the original file it came from. Every
 * original line appears exactly once in the parser text.
 *
 * An exported PROPERTY also has no END_PROPERTY; one is appended to its last
 * END_GET/END_SET line (no line is added), and a ';' right after a member
 * terminator is blanked (the grammar would take it for a body statement).
 *
 * The parser text is also dialect-normalized (cbm_st_normalize), which never
 * moves a line. A source without trailing members keeps an identity line map
 * (src_line == NULL) and costs no copy beyond the normalization.
 */

#include <stdbool.h>
#include <stdint.h>

typedef struct {
    char *text;         /* parser text, NUL-terminated, cbm_alloc'd (EXTRACT) */
    int len;            /* bytes in text, without the NUL */
    uint32_t *src_line; /* src_line[k] = original line of parser line k + 1; NULL = identity */
    uint32_t lines;     /* entries in src_line */
} CBMStUnit;

/* Build the parser text of `src`. Returns false (and leaves *out empty) only
 * when not even the normalized text could be allocated; a failed reorder
 * falls back to the normalized text with an identity map. */
bool cbm_st_unit_build(const char *src, int len, CBMStUnit *out);

/* Original 1-based line of 1-based parser line `parser_line`; 0 stays 0 and a
 * line past the map clamps to its last entry. */
uint32_t cbm_st_unit_line(const CBMStUnit *u, uint32_t parser_line);

/* Map `n` parser-line ranges [starts[i], ends[i]] to original-line ranges:
 * each splits where the map jumps, then all are sorted by start and merged
 * when they overlap or touch. Writes at most `cap` ranges to out_starts /
 * out_ends, returns how many, and adds the ranges that did not fit to
 * *dropped. */
int cbm_st_unit_map_ranges(const CBMStUnit *u, const uint32_t *starts, const uint32_t *ends, int n,
                           uint32_t *out_starts, uint32_t *out_ends, int cap, int *dropped);

/* Release everything the unit owns and zero it. */
void cbm_st_unit_free(CBMStUnit *u);

#endif /* CBM_ST_UNIT_H */
