#ifndef CBM_TWINCAT_XML_H
#define CBM_TWINCAT_XML_H

/*
 * TwinCAT PLC object XML (.TcPOU/.TcDUT/.TcGVL/.TcIO) -> IEC 61131-3 Structured Text.
 *
 * A TwinCAT object file splits one POU across sibling XML elements: the POU
 * <Declaration> carries "FUNCTION_BLOCK X ... VAR ... END_VAR" without an
 * END_FUNCTION_BLOCK, its body sits in <Implementation><ST>, and every Method
 * and Property accessor carries its own declaration and body. The ST grammar
 * can only read the POU once it is reassembled PER FILE with the members ahead
 * of the body statements, and once the TwinCAT dialect the grammar excludes
 * (pragmas, REFERENCE TO, access modifiers on POUs, constructor arguments, ...)
 * is normalized away. Measured over 1380 real files: 84.9 % parse errors raw,
 * 4.8 % after this transcoding.
 *
 * Every transform preserves the number and order of newlines, so each line of
 * the generated ST maps to exactly one line of the XML file; `xml_line`
 * records that mapping for reporting definitions at their real file position.
 */

#include <stdbool.h>
#include <stdint.h>

typedef struct {
    char *text;          /* assembled + normalized ST, NUL-terminated (heap) */
    int len;             /* strlen(text) */
    uint32_t *xml_line;  /* xml_line[i] = 1-based XML line of ST line i+1 (heap) */
    uint32_t line_count; /* entries in xml_line */
    uint32_t xml_lines;  /* line count of the XML file itself */
} CBMTwinCATUnit;

/* Transcode one TwinCAT object file. Returns false when the file holds no
 * POU/DUT/GVL/Itf object with a recognizable declaration keyword, or on
 * allocation failure; `out` is then zeroed and needs no free. */
bool cbm_twincat_to_st(const char *xml, int xml_len, CBMTwinCATUnit *out);

void cbm_twincat_unit_free(CBMTwinCATUnit *unit);

/* The dialect normalization on its own (exposed for tests). Returns a heap
 * NUL-terminated buffer holding exactly as many newlines as `src`, or NULL on
 * allocation failure. */
char *cbm_twincat_normalize(const char *src, int len, int *out_len);

/* Map a 1-based ST line to its 1-based XML line (clamped into range). */
uint32_t cbm_twincat_xml_line(const CBMTwinCATUnit *unit, uint32_t st_line);

#endif /* CBM_TWINCAT_XML_H */
