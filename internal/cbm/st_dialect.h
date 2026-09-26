#ifndef CBM_ST_DIALECT_H
#define CBM_ST_DIALECT_H

/*
 * Vendor-dialect normalization for IEC 61131-3 Structured Text (.st).
 *
 * Real .st exports (CODESYS, TwinCAT) carry constructs the ST grammar rejects
 * by design: pragmas ({attribute ...}, {warning ...}), an enum's integer base
 * type, REFERENCE TO, access modifiers on POUs, constructor arguments and
 * array initializers inside declarations, PERSISTENT, AND_THEN/OR_ELSE,
 * hardware address bindings (AT %I*), ARRAY[*], sized STRING[n]/WSTRING[n],
 * and TYPE ... EXTENDS.
 *
 * Every pass preserves the number and order of newlines, so line N of the
 * normalized source is still line N of the original file: definitions are
 * reported at their real source position without any line remap.
 */

/* Normalize one .st source. Returns a heap NUL-terminated buffer holding
 * exactly as many newlines as `src`, or NULL on allocation failure; the
 * caller frees it with cbm_free(CBM_MEM_CLASS_EXTRACT, p). */
char *cbm_st_normalize(const char *src, int len, int *out_len);

#endif /* CBM_ST_DIALECT_H */
