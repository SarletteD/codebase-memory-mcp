/*
 * twincat_ns.c — resolve namespace-qualified TwinCAT base names through their library.
 *
 * A TwinCAT project references a library under a namespace alias declared in its
 * .plcproj:
 *
 *   <PlaceholderReference Include="LibVendorCore">
 *     <DefaultResolution>LibVendorCore, * (Vendor Inc.)</DefaultResolution>
 *     <Namespace>Vnd_Core</Namespace>
 *
 * so `FUNCTION_BLOCK FB_X EXTENDS Vnd_Core.FB_Base` names FB_Base of the library whose
 * .plcproj carries <Title>LibVendorCore</Title>. The same short name often exists in
 * several libraries of one tree (I_EventAddValues in LibVendorUtilities AND in
 * LibVendorCore), so a qualified base is resolved ONLY inside the aliased library:
 * no last-segment fallback, and more than one candidate there means no edge.
 *
 * .plcproj files are not indexed; they are read from disk on first use and cached
 * per directory. Only qualified bases of TwinCAT definitions reach this code, so a
 * repository without TwinCAT never touches the disk here. The cache is shared by
 * the parallel resolve workers and therefore guarded by a mutex.
 */
#include "foundation/constants.h"
#include "pipeline/pipeline.h"
#include "pipeline/pipeline_internal.h"
#include "graph_buffer/graph_buffer.h"
#include "foundation/compat.h"
#include "foundation/compat_fs.h"
#include "foundation/compat_thread.h"
#include "foundation/hash_table.h"
#include "cbm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Upper bound for a .plcproj read into memory (a 1,300-object project's largest is ~0.2 MB). */
#define TC_NS_PLCPROJ_MAX_BYTES (16 * 1024 * 1024)
/* Path buffers: repository root + relative directory + file name. */
#define TC_NS_PATH_MAX 4096

typedef struct {
    char *title;   /* library identity: <Title>, else <Name>, else file stem */
    char **alias;  /* namespace alias as declared */
    char **target; /* title of the library the alias resolves to */
    int ref_count;
} tc_project_t;

struct cbm_tc_ns {
    char *repo_path;
    cbm_mutex_t mu;
    CBMHashTable *dir_project; /* rel dir ("" = root) → tc_project_t*, or &TC_NO_PROJECT */
    tc_project_t **projects;   /* owned */
    int project_count;
};

/* Cache value for "no single .plcproj governs this directory". */
static tc_project_t TC_NO_PROJECT;

static bool ci_equal_n(const char *a, size_t alen, const char *b) {
    size_t blen = strlen(b);
    if (alen != blen) {
        return false;
    }
    for (size_t i = 0; i < alen; i++) {
        char x = a[i];
        char y = b[i];
        if (x >= 'a' && x <= 'z') {
            x = (char)(x - 'a' + 'A');
        }
        if (y >= 'a' && y <= 'z') {
            y = (char)(y - 'a' + 'A');
        }
        if (x != y) {
            return false;
        }
    }
    return true;
}

static bool ends_with_ci(const char *s, const char *suffix) {
    size_t n = strlen(s);
    size_t k = strlen(suffix);
    return n >= k && ci_equal_n(s + n - k, k, suffix);
}

static bool is_ws(char c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

/* Heap copy of [s, s+len) without surrounding whitespace. */
static char *dup_trimmed(const char *s, size_t len) {
    while (len > 0 && is_ws(*s)) {
        s++;
        len--;
    }
    while (len > 0 && is_ws(s[len - 1])) {
        len--;
    }
    char *out = malloc(len + 1);
    if (out) {
        memcpy(out, s, len);
        out[len] = '\0';
    }
    return out;
}

/* Library title of a resolution string "LibVendorIo, 0.1.7 (Vendor)" → "LibVendorIo". */
static char *title_of_resolution(const char *s, size_t len) {
    const char *comma = memchr(s, ',', len);
    return dup_trimmed(s, comma ? (size_t)(comma - s) : len);
}

/* Find "<tag>" in [from, end); returns the inner text start and its length, or NULL. */
static const char *xml_inner(const char *from, const char *end, const char *tag, size_t *len) {
    char open[CBM_SZ_64];
    char close[CBM_SZ_64];
    snprintf(open, sizeof(open), "<%s>", tag);
    snprintf(close, sizeof(close), "</%s>", tag);
    size_t olen = strlen(open);
    size_t clen = strlen(close);
    for (const char *p = from; p + olen <= end; p++) {
        if (memcmp(p, open, olen) != 0) {
            continue;
        }
        const char *inner = p + olen;
        for (const char *q = inner; q + clen <= end; q++) {
            if (memcmp(q, close, clen) == 0) {
                *len = (size_t)(q - inner);
                return inner;
            }
        }
        return NULL;
    }
    return NULL;
}

/* Find the next "<elem Include="...">…</elem>" in [from, end). Returns the start of the
 * element, sets the Include value and the element body [*body, *body_end), or NULL. */
static const char *xml_include_elem(const char *from, const char *end, const char *elem,
                                    const char **inc, size_t *inc_len, const char **body,
                                    const char **body_end) {
    char open[CBM_SZ_64];
    char close[CBM_SZ_64];
    snprintf(open, sizeof(open), "<%s ", elem);
    snprintf(close, sizeof(close), "</%s>", elem);
    size_t olen = strlen(open);
    size_t clen = strlen(close);
    static const char INCLUDE[] = "Include=\"";
    size_t ilen = sizeof(INCLUDE) - 1;
    for (const char *p = from; p + olen <= end; p++) {
        if (memcmp(p, open, olen) != 0) {
            continue;
        }
        const char *gt = memchr(p, '>', (size_t)(end - p));
        if (!gt) {
            return NULL;
        }
        const char *attr = NULL;
        for (const char *a = p + olen; a + ilen <= gt; a++) {
            if (memcmp(a, INCLUDE, ilen) == 0) {
                attr = a + ilen;
                break;
            }
        }
        const char *quote = attr ? memchr(attr, '"', (size_t)(gt - attr)) : NULL;
        if (!quote) {
            continue;
        }
        *inc = attr;
        *inc_len = (size_t)(quote - attr);
        *body = gt + 1;
        *body_end = gt + 1;
        if (gt[-1] != '/') {
            for (const char *q = gt + 1; q + clen <= end; q++) {
                if (memcmp(q, close, clen) == 0) {
                    *body_end = q;
                    break;
                }
            }
        }
        return p;
    }
    return NULL;
}

static void project_free(tc_project_t *p) {
    if (!p) {
        return;
    }
    for (int i = 0; i < p->ref_count; i++) {
        free(p->alias[i]);
        free(p->target[i]);
    }
    free(p->alias);
    free(p->target);
    free(p->title);
    free(p);
}

static void project_add_ref(tc_project_t *p, char *alias, char *target) {
    if (!alias || !target || !alias[0] || !target[0]) {
        free(alias);
        free(target);
        return;
    }
    char **na = realloc(p->alias, (size_t)(p->ref_count + 1) * sizeof(char *));
    if (na) {
        p->alias = na;
    }
    char **nt = realloc(p->target, (size_t)(p->ref_count + 1) * sizeof(char *));
    if (nt) {
        p->target = nt;
    }
    if (!na || !nt) {
        free(alias);
        free(target);
        return;
    }
    p->alias[p->ref_count] = alias;
    p->target[p->ref_count] = target;
    p->ref_count++;
}

/* Title a placeholder resolves to: its <PlaceholderResolution>, else its
 * <DefaultResolution>, else the placeholder name itself. */
static char *placeholder_title(const char *s, const char *end, const char *inc, size_t inc_len,
                               const char *body, const char *body_end) {
    const char *from = s;
    const char *rinc = NULL;
    size_t rinc_len = 0;
    const char *rbody = NULL;
    const char *rbody_end = NULL;
    const char *at;
    while ((at = xml_include_elem(from, end, "PlaceholderResolution", &rinc, &rinc_len, &rbody,
                                  &rbody_end)) != NULL) {
        if (rinc_len == inc_len && memcmp(rinc, inc, inc_len) == 0) {
            size_t len = 0;
            const char *res = xml_inner(rbody, rbody_end, "Resolution", &len);
            if (res) {
                return title_of_resolution(res, len);
            }
        }
        from = at + 1;
    }
    size_t len = 0;
    const char *dflt = xml_inner(body, body_end, "DefaultResolution", &len);
    return dflt ? title_of_resolution(dflt, len) : dup_trimmed(inc, inc_len);
}

static tc_project_t *project_parse(const char *s, size_t n, const char *file_name) {
    tc_project_t *p = calloc(1, sizeof(*p));
    if (!p) {
        return NULL;
    }
    const char *end = s + n;
    size_t len = 0;
    const char *t = xml_inner(s, end, "Title", &len);
    if (!t) {
        t = xml_inner(s, end, "Name", &len);
    }
    if (t) {
        p->title = dup_trimmed(t, len);
    } else {
        const char *dot = strrchr(file_name, '.');
        p->title = dup_trimmed(file_name, dot ? (size_t)(dot - file_name) : strlen(file_name));
    }

    const char *inc = NULL;
    size_t inc_len = 0;
    const char *body = NULL;
    const char *body_end = NULL;
    const char *from = s;
    const char *at;
    while ((at = xml_include_elem(from, end, "PlaceholderReference", &inc, &inc_len, &body,
                                  &body_end)) != NULL) {
        const char *ns = xml_inner(body, body_end, "Namespace", &len);
        if (ns) {
            project_add_ref(p, dup_trimmed(ns, len),
                            placeholder_title(s, end, inc, inc_len, body, body_end));
        }
        from = at + 1;
    }
    from = s;
    while ((at = xml_include_elem(from, end, "LibraryReference", &inc, &inc_len, &body,
                                  &body_end)) != NULL) {
        const char *ns = xml_inner(body, body_end, "Namespace", &len);
        if (ns) {
            project_add_ref(p, dup_trimmed(ns, len), title_of_resolution(inc, inc_len));
        }
        from = at + 1;
    }
    return p;
}

static tc_project_t *project_load(cbm_tc_ns_t *ns, const char *path, const char *file_name) {
    FILE *f = cbm_fopen(path, "rb");
    if (!f) {
        return NULL;
    }
    char *buf = NULL;
    size_t n = 0;
    if (fseek(f, 0, SEEK_END) == 0) {
        long size = ftell(f);
        if (size > 0 && size <= TC_NS_PLCPROJ_MAX_BYTES && fseek(f, 0, SEEK_SET) == 0) {
            buf = malloc((size_t)size);
            if (buf) {
                n = fread(buf, 1, (size_t)size, f);
            }
        }
    }
    fclose(f);
    if (!buf) {
        return NULL;
    }
    tc_project_t *p = project_parse(buf, n, file_name);
    free(buf);
    if (!p || !p->title) {
        project_free(p);
        return NULL;
    }
    tc_project_t **grown =
        realloc(ns->projects, (size_t)(ns->project_count + 1) * sizeof(tc_project_t *));
    if (!grown) {
        project_free(p);
        return NULL;
    }
    ns->projects = grown;
    ns->projects[ns->project_count++] = p;
    return p;
}

/* The project governing rel_dir: the .plcproj in that directory or, when there is
 * none, in the nearest ancestor up to the repository root. A directory holding more
 * than one .plcproj governs nothing. Caller holds ns->mu. */
static const tc_project_t *project_of_dir(cbm_tc_ns_t *ns, const char *rel_dir) {
    if (!ns->dir_project) {
        ns->dir_project = cbm_ht_create(0);
        if (!ns->dir_project) {
            return NULL;
        }
    }
    tc_project_t *cached = cbm_ht_get(ns->dir_project, rel_dir);
    if (cached) {
        return cached == &TC_NO_PROJECT ? NULL : cached;
    }

    char abs[TC_NS_PATH_MAX];
    int w = rel_dir[0] ? snprintf(abs, sizeof(abs), "%s/%s", ns->repo_path, rel_dir)
                       : snprintf(abs, sizeof(abs), "%s", ns->repo_path);
    tc_project_t *found = NULL;
    int plcproj_count = 0;
    char file_name[CBM_DIRENT_NAME_MAX];
    if (w > 0 && (size_t)w < sizeof(abs)) {
        cbm_dir_t *d = cbm_opendir(abs);
        if (d) {
            cbm_dirent_t *e;
            while ((e = cbm_readdir(d)) != NULL) {
                if (!e->is_dir && ends_with_ci(e->name, ".plcproj")) {
                    plcproj_count++;
                    snprintf(file_name, sizeof(file_name), "%s", e->name);
                }
            }
            cbm_closedir(d);
        }
    }
    if (plcproj_count == 1) {
        char path[TC_NS_PATH_MAX];
        int pw = snprintf(path, sizeof(path), "%s/%s", abs, file_name);
        if (pw > 0 && (size_t)pw < sizeof(path)) {
            found = project_load(ns, path, file_name);
        }
    } else if (plcproj_count == 0 && rel_dir[0]) {
        char parent[TC_NS_PATH_MAX];
        snprintf(parent, sizeof(parent), "%s", rel_dir);
        char *slash = strrchr(parent, '/');
        if (slash) {
            *slash = '\0';
        } else {
            parent[0] = '\0';
        }
        found = (tc_project_t *)project_of_dir(ns, parent);
    }

    char *key = strdup(rel_dir);
    if (key) {
        cbm_ht_set(ns->dir_project, key, found ? found : &TC_NO_PROJECT);
    }
    return found;
}

static const tc_project_t *project_of_file(cbm_tc_ns_t *ns, const char *rel_path) {
    char dir[TC_NS_PATH_MAX];
    snprintf(dir, sizeof(dir), "%s", rel_path);
    for (char *c = dir; *c; c++) {
        if (*c == '\\') {
            *c = '/';
        }
    }
    char *slash = strrchr(dir, '/');
    if (slash) {
        *slash = '\0';
    } else {
        dir[0] = '\0';
    }
    return project_of_dir(ns, dir);
}

cbm_tc_ns_t *cbm_tc_ns_new(const char *repo_path) {
    if (!repo_path || !repo_path[0]) {
        return NULL;
    }
    cbm_tc_ns_t *ns = calloc(1, sizeof(*ns));
    if (!ns) {
        return NULL;
    }
    ns->repo_path = strdup(repo_path);
    if (!ns->repo_path) {
        free(ns);
        return NULL;
    }
    cbm_mutex_init(&ns->mu);
    return ns;
}

static void free_key(const char *key, void *value, void *userdata) {
    (void)value;
    (void)userdata;
    free((void *)key);
}

void cbm_tc_ns_free(cbm_tc_ns_t *ns) {
    if (!ns) {
        return;
    }
    if (ns->dir_project) {
        cbm_ht_foreach(ns->dir_project, free_key, NULL);
        cbm_ht_free(ns->dir_project);
    }
    for (int i = 0; i < ns->project_count; i++) {
        project_free(ns->projects[i]);
    }
    free(ns->projects);
    cbm_mutex_destroy(&ns->mu);
    free(ns->repo_path);
    free(ns);
}

bool cbm_tc_ns_same_library(cbm_tc_ns_t *ns, const char *rel_a, const char *rel_b) {
    if (!ns || !rel_a || !rel_b) {
        return false;
    }
    cbm_mutex_lock(&ns->mu);
    const tc_project_t *a = project_of_file(ns, rel_a);
    const tc_project_t *b = project_of_file(ns, rel_b);
    cbm_mutex_unlock(&ns->mu);
    return a && b && a == b;
}

bool cbm_tc_ns_applies(CBMLanguage lang, const char *base) {
    return lang == CBM_LANG_TWINCAT && base && strchr(base, '.') != NULL;
}

const char *cbm_tc_ns_resolve_base(cbm_tc_ns_t *ns, const cbm_registry_t *reg,
                                   const cbm_gbuf_t *gbuf, const char *rel_path,
                                   const char *base) {
    const char *dot = base ? strrchr(base, '.') : NULL;
    if (!ns || !reg || !gbuf || !rel_path || !dot || dot == base || dot[1] == '\0') {
        return NULL;
    }
    /* `A.B.C` (a nested namespace) does not occur in the measured corpus: refuse it
     * rather than guess which part names the library. */
    if (memchr(base, '.', (size_t)(dot - base)) != NULL) {
        return NULL;
    }
    const char *alias = base;
    size_t alias_len = (size_t)(dot - base);
    const char *short_name = dot + 1;

    const char *hit = NULL;
    int hits = 0;
    cbm_mutex_lock(&ns->mu);
    const tc_project_t *src = project_of_file(ns, rel_path);
    const char *library = NULL;
    for (int i = 0; src && i < src->ref_count; i++) {
        /* ST identifiers are case-insensitive: real projects spell `VND_Util.` next to `Vnd_Util`. */
        if (ci_equal_n(alias, alias_len, src->alias[i])) {
            library = src->target[i];
            break;
        }
    }
    const char **qns = NULL;
    int qn_count = 0;
    if (library) {
        cbm_registry_find_by_name(reg, short_name, &qns, &qn_count);
    }
    for (int i = 0; i < qn_count; i++) {
        if (!cbm_label_is_type_like(cbm_registry_label_of(reg, qns[i]))) {
            continue;
        }
        const cbm_gbuf_node_t *node = cbm_gbuf_find_by_qn(gbuf, qns[i]);
        if (!node || !node->file_path) {
            continue;
        }
        const tc_project_t *owner = project_of_file(ns, node->file_path);
        if (!owner || !ci_equal_n(owner->title, strlen(owner->title), library)) {
            continue;
        }
        if (!hit || strcmp(hit, qns[i]) != 0) {
            hit = qns[i];
            hits++;
        }
    }
    cbm_mutex_unlock(&ns->mu);
    return hits == 1 ? hit : NULL;
}
