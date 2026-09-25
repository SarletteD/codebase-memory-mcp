/*
 * test_edge_structural.c — Pipeline / edge-CREATION reproduction suite.
 *
 * ════════════════════════════════════════════════════════════════════
 * PURPOSE
 * ────────
 * Comprehensively probe whether the GRAPH PIPELINE creates each non-import
 * edge type for each hybrid-LSP language, with special emphasis on CROSS-FILE
 * scenarios where the resolver must map a bare name in file B to a definition
 * node living in file A.
 *
 * This is distinct from the extraction-level suites (test_extraction.c,
 * test_extraction_inheritance.c, test_extraction_imports.c) which test whether
 * cbm_extract_file() populates the right fields.  Here we run the FULL
 * production pipeline (index_repository via MCP) and assert the resulting
 * graph DB contains the expected edges via cbm_store_count_edges_by_type.
 *
 * The companion file test_edge_imports.c (another workstream) covers IMPORTS
 * edge creation.  This file covers every OTHER edge type.
 *
 * ════════════════════════════════════════════════════════════════════
 * EXPECTED GREEN vs RED — REASONING
 * ──────────────────────────────────
 *
 * CALLS (cross-file):
 *   All 9 hybrid-LSP languages use the generic name-based resolver
 *   (pass_calls.c).  The resolver populates the registry with all defs first,
 *   then matches call sites by name.  Cross-file is structurally identical to
 *   same-file from the resolver's perspective (registry is project-wide).
 *   CALLS resolve at 99.6–100% on real repos, so all 9 languages are expected
 *   GREEN.  Any RED would be a real regression.
 *
 * INHERITS (cross-file class extends):
 *   Resolution requires: (a) base_classes extracted correctly at the
 *   extraction layer, AND (b) the registry resolving that bare name to the
 *   correct Class node in the other file.  Known extraction bugs (documented
 *   in test_extraction_inheritance.c):
 *     Python   — simple `class Dog(Animal):` broken; base_classes holds "(Animal)"
 *                with parens — extraction RED → INHERITS edge RED.
 *     TypeScript — extractor stores "extends" keyword not the type name → RED.
 *     PHP      — base_classes never populated → RED.
 *     Kotlin   — `:` supertype syntax not parsed → RED.
 *   Expected GREEN (extraction works):
 *     Java, C#, C++  — extraction correct per test_extraction_inheritance.c.
 *     Rust     — uses impl_traits not base_classes; IMPLEMENTS path, not
 *                INHERITS.  No INHERITS expected.
 *     Go       — struct embedding / interface satisfaction uses IMPLEMENTS not
 *                INHERITS in the Go semantic pass.
 *
 * IMPLEMENTS (interface):
 *   Rust `impl Trait for Struct` cross-file: trait in a.rs, impl in b.rs.
 *     The resolve_impl_traits pass uses registry lookup for both trait_name and
 *     struct_name.  If both are in the registry (from definitions pass), the edge
 *     is created.  Expected GREEN when both files are indexed.
 *   Java `implements` interface (same-file): extraction stores base_classes; the
 *     semantic pass creates INHERITS for `extends` and IMPLEMENTS for interfaces
 *     (pass_parallel.c line ~1943).  Expected GREEN same-file, RED cross-file
 *     until the resolver properly distinguishes Class vs Interface targets.
 *   Go implicit interface satisfaction: pass_semantic.c cbm_pipeline_implements_go()
 *     is triggered only when the struct's method-set fully covers the interface's.
 *     Expected GREEN when struct methods and interface are in same index.
 *   C# `class X : IFoo`: extraction stores base_classes; same INHERITS/IMPLEMENTS
 *     resolution path as Java.  Same-file expected GREEN.
 *
 * DECORATES (cross-file decorator):
 *   Python: decorator resolved via import map + registry.  Cross-file requires
 *     an IMPORTS edge resolution that in turn requires the decorator to be in the
 *     registry.  Expected GREEN for same-file (existing P6 contract confirms this).
 *     Cross-file expected GREEN if relative import resolves (Python OK for
 *     relative imports per P3).
 *   TypeScript: TS decorator (class decorator).  TS extraction captures
 *     decorators array.  Expected GREEN same-file.
 *   Java annotations: Java extraction may not populate decorators[].  Expected
 *     RED (unconfirmed — annotated as uncertain).
 *   Kotlin annotations: Kotlin extraction status unclear → tentatively RED.
 *   C# attributes: C# extraction unclear → tentatively RED.
 *
 * USAGE (cross-file type usage):
 *   The USAGE pass (pass_usages.c) creates edges when a type/symbol reference
 *   (not a call) resolves in the registry.  Expected GREEN for languages where
 *   usages are extracted (Python, Go, TS).  Uncertain for Java/C#/Kotlin/PHP/Rust
 *   where USAGE extraction coverage is unclear.
 *
 * DATA_FLOWS:
 *   Created by pass_data_flows.c via Route intermediation (HTTP_CALLS + HANDLES
 *   on the same route path).  Not per-language — fixture-driven.  Existing P6
 *   contract covers same-file.  This suite adds a cross-file variant.
 *
 * OVERRIDE (Go interface method):
 *   Created by pass_semantic.c when a Go struct satisfies an interface; each
 *   implementing method gets an OVERRIDE edge to the interface method.  Expected
 *   GREEN for Go with a struct + interface pair in the same index.
 *
 * TESTS (function-level test->production function):
 *   pass_tests.c creates this.  Existing P6 covers Go.  This suite adds Python
 *   and TypeScript cross-file variants.
 *
 * ════════════════════════════════════════════════════════════════════
 * SUITE STRUCTURE
 * ───────────────
 * Edge family                       Languages / cases         Expected
 * ─────────────────────────────────────────────────────────────────
 * CALLS cross-file                  Go/C/C++/Rust/Python/     9 GREEN
 *                                   TS/Java/Kotlin/C#
 * INHERITS cross-file               Java/C#/C++               3 GREEN
 *                                   Python/TS/PHP/Kotlin       4 RED
 * IMPLEMENTS cross-file             Rust                      1 GREEN
 * IMPLEMENTS same-file interface    Java/C#/Go                3 GREEN (uncertain)
 * DECORATES same-file               Python/TS                  2 GREEN
 * DECORATES cross-file              Python                     1 GREEN
 * DECORATES annotations             Java/Kotlin/C#             3 uncertain→RED
 * USAGE cross-file                  Python/TS/Go               3 GREEN (uncertain)
 * DATA_FLOWS cross-file             Python                     1 GREEN
 * OVERRIDE (Go implicit iface)      Go                         1 GREEN
 * TESTS cross-file                  Python/TypeScript          2 GREEN
 *
 * Total test functions: 24
 *
 * NOTE: "Do NOT register in test_main.c" — this suite is SEPARATE from the
 * existing lang_contract suite.  The SUITE(edge_structural) macro defines
 * suite_edge_structural() which can be wired up independently.
 */

#include "../src/foundation/compat.h"
#include "test_framework.h"
#include "test_helpers.h"
#include "cbm.h"
#include <mcp/mcp.h>
#include <store/store.h>
#include <pipeline/pipeline.h>
#include <foundation/log.h>

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#if !defined(_WIN32)
#include <sys/wait.h>
#endif

/* ══════════════════════════════════════════════════════════════════
 * Harness (copy of the pattern from test_lang_contract.c — these
 * helpers are static so each translation unit is self-contained).
 * ══════════════════════════════════════════════════════════════════ */

typedef struct {
    char tmpdir[256];
    char dbpath[512];
    char *project;
    cbm_mcp_server_t *srv;
} ES_LangProj;

typedef struct {
    const char *name;
    const char *content;
} ES_LangFile;

static void es_lc_to_fwd_slashes(char *p) {
    for (; *p; p++) {
        if (*p == '\\') {
            *p = '/';
        }
    }
}

static cbm_store_t *es_lang_open_indexed(ES_LangProj *lp) {
    lp->project = cbm_project_name_from_path(lp->tmpdir);
    if (!lp->project) {
        return NULL;
    }
    const char *home = getenv("HOME");
    if (!home) {
        home = "/tmp";
    }
    char cache_dir[512];
    snprintf(cache_dir, sizeof(cache_dir), "%s/.cache/codebase-memory-mcp", home);
    cbm_mkdir(cache_dir);
    snprintf(lp->dbpath, sizeof(lp->dbpath), "%s/%s.db", cache_dir, lp->project);
    unlink(lp->dbpath);
    lp->srv = cbm_mcp_server_new(NULL);
    if (!lp->srv) {
        return NULL;
    }
    char args[700];
    snprintf(args, sizeof(args), "{\"repo_path\":\"%s\"}", lp->tmpdir);
    char *resp = cbm_mcp_handle_tool(lp->srv, "index_repository", args);
    if (resp) {
        free(resp);
    }
    return cbm_store_open_path(lp->dbpath);
}

static cbm_store_t *es_lang_index_files(ES_LangProj *lp, const ES_LangFile *files, int nfiles) {
    memset(lp, 0, sizeof(*lp));
    snprintf(lp->tmpdir, sizeof(lp->tmpdir), "/tmp/cbm_es_XXXXXX");
    if (!cbm_mkdtemp(lp->tmpdir)) {
        return NULL;
    }
    es_lc_to_fwd_slashes(lp->tmpdir);
    for (int i = 0; i < nfiles; i++) {
        char path[700];
        snprintf(path, sizeof(path), "%s/%s", lp->tmpdir, files[i].name);
        char *slash = strrchr(path, '/');
        if (slash && slash > path + strlen(lp->tmpdir)) {
            *slash = '\0';
            cbm_mkdir_p(path, 0755);
            *slash = '/';
        }
        FILE *f = fopen(path, "wb");
        if (!f) {
            return NULL;
        }
        fputs(files[i].content, f);
        fclose(f);
    }
    return es_lang_open_indexed(lp);
}

static void es_lang_cleanup(ES_LangProj *lp, cbm_store_t *store) {
    if (store) {
        cbm_store_close(store);
    }
    if (lp->srv) {
        cbm_mcp_server_free(lp->srv);
        lp->srv = NULL;
    }
    free(lp->project);
    lp->project = NULL;
    th_rmtree(lp->tmpdir);
    unlink(lp->dbpath);
    char wal[600];
    char shm[600];
    snprintf(wal, sizeof(wal), "%s-wal", lp->dbpath);
    unlink(wal);
    snprintf(shm, sizeof(shm), "%s-shm", lp->dbpath);
    unlink(shm);
}

/* Every graph edge type the pipeline can emit — used in diagnostic dumps. */
static const char *ES_ALL_EDGE_TYPES[] = {"CALLS",
                                          "CALL_REFERENCE",
                                          "CONFIGURES",
                                          "CONTAINS_FILE",
                                          "CONTAINS_FOLDER",
                                          "DATA_FLOWS",
                                          "DECORATES",
                                          "DEFINES",
                                          "DEFINES_METHOD",
                                          "DEPENDS_ON",
                                          "FILE_CHANGES_WITH",
                                          "GRAPHQL_CALLS",
                                          "GRPC_CALLS",
                                          "HANDLES",
                                          "HTTP_CALLS",
                                          "IMPLEMENTS",
                                          "IMPORTS",
                                          "INHERITS",
                                          "INFRA_MAPS",
                                          "OVERRIDE",
                                          "SEMANTICALLY_RELATED",
                                          "SIMILAR_TO",
                                          "TESTS_FILE",
                                          "TESTS",
                                          "TRPC_CALLS",
                                          "USAGE",
                                          "ASYNC_CALLS",
                                          NULL};

static void es_dump_edge_histogram(cbm_store_t *store, const char *project) {
    if (!store) {
        fprintf(stderr, "      └─ (no graph DB)\n");
        return;
    }
    char line[640] = {0};
    for (int i = 0; ES_ALL_EDGE_TYPES[i]; i++) {
        int c = cbm_store_count_edges_by_type(store, project, ES_ALL_EDGE_TYPES[i]);
        if (c > 0 && strlen(line) < sizeof(line) - 48) {
            char one[64];
            snprintf(one, sizeof(one), "%s=%d ", ES_ALL_EDGE_TYPES[i], c);
            strncat(line, one, sizeof(line) - strlen(line) - 1);
        }
    }
    fprintf(stderr, "      └─ edges: [%s]\n", line[0] ? line : "(none)");
}

/* Index `files`, assert `edge` appears at least `floor` times.
 * On failure, dump the full edge histogram. */
static int es_edge_present(const ES_LangFile *files, int nfiles, const char *edge, int floor) {
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, files, nfiles);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, edge) : -1;
    if (got < floor) {
        fprintf(stderr, "  [ES-EDGE] FAIL %-20s got=%d expected>=%d\n", edge, got, floor);
        es_dump_edge_histogram(store, lp.project);
    }
    es_lang_cleanup(&lp, store);
    return got >= floor;
}

static int es_exact_edge_by_name(const ES_LangFile *files, int nfiles, const char *edge_type,
                                 const char *source_name, const char *target_name) {
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, files, nfiles);
    cbm_node_t *sources = NULL;
    cbm_node_t *targets = NULL;
    int source_count = 0;
    int target_count = 0;
    int matches = -1;
    if (store &&
        cbm_store_find_nodes_by_name(store, lp.project, source_name, &sources, &source_count) ==
            CBM_STORE_OK &&
        cbm_store_find_nodes_by_name(store, lp.project, target_name, &targets, &target_count) ==
            CBM_STORE_OK &&
        source_count == 1 && target_count == 1) {
        cbm_edge_t *edges = NULL;
        int edge_count = 0;
        if (cbm_store_find_edges_by_source_type(store, sources[0].id, edge_type, &edges,
                                                &edge_count) == CBM_STORE_OK) {
            matches = 0;
            for (int i = 0; i < edge_count; i++) {
                if (edges[i].target_id == targets[0].id) {
                    matches++;
                }
            }
        }
        cbm_store_free_edges(edges, edge_count);
    }
    cbm_store_free_nodes(sources, source_count);
    cbm_store_free_nodes(targets, target_count);
    es_lang_cleanup(&lp, store);
    return matches;
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 1: CALLS cross-file
 *
 * Function defined in file A, called from file B.  The registry is
 * project-wide so cross-file is identical to same-file for the resolver.
 * ALL 9 hybrid-LSP languages are expected GREEN.
 * ══════════════════════════════════════════════════════════════════ */

/* Go: caller in main.go, callee in util.go — same package. */
TEST(es_calls_crossfile_go) {
    static const ES_LangFile f[] = {
        {"util.go",
         "package svc\n\nfunc Compute(x int) int {\n\treturn x * 2\n}\n"},
        {"main.go",
         "package svc\n\nfunc Run(y int) int {\n\treturn Compute(y + 1)\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* Run -> Compute */
    PASS();
}

/* C: caller in main.c, callee declared/defined in util.c. */
TEST(es_calls_crossfile_c) {
    static const ES_LangFile f[] = {
        {"util.c",
         "int add(int a, int b) {\n    return a + b;\n}\n"},
        {"main.c",
         "int add(int a, int b);\n\nint run(int x) {\n    return add(x, 1);\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> add */
    PASS();
}

/* C++: caller in main.cpp, callee in util.cpp. */
TEST(es_calls_crossfile_cpp) {
    static const ES_LangFile f[] = {
        {"util.cpp",
         "int multiply(int a, int b) {\n    return a * b;\n}\n"},
        {"main.cpp",
         "int multiply(int a, int b);\n\nint run(int x) {\n    return multiply(x, 3);\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> multiply */
    PASS();
}

/* Rust: caller in main.rs, callee in lib.rs (pub fn). */
TEST(es_calls_crossfile_rust) {
    static const ES_LangFile f[] = {
        {"lib.rs",
         "pub fn square(x: i32) -> i32 {\n    x * x\n}\n"},
        {"main.rs",
         "mod lib;\n\nfn run(n: i32) -> i32 {\n    lib::square(n)\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> square */
    PASS();
}

/* Python: caller in main.py calls function from util.py via relative import. */
TEST(es_calls_crossfile_python) {
    static const ES_LangFile f[] = {
        {"util.py",
         "def transform(x):\n    return x * 3\n"},
        {"main.py",
         "from .util import transform\n\n\ndef run(y):\n    return transform(y)\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> transform */
    PASS();
}

/* TypeScript: caller in main.ts calls function from util.ts. */
TEST(es_calls_crossfile_typescript) {
    static const ES_LangFile f[] = {
        {"util.ts",
         "export function format(s: string): string {\n    return s.trim();\n}\n"},
        {"main.ts",
         "import { format } from './util';\n\n"
         "export function run(input: string): string {\n    return format(input);\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> format */
    PASS();
}

TEST(es_calls_vue_embedded_issue1410) {
    static const ES_LangFile f[] = {
        {"App.vue",
         "<template><p>Vue</p></template>\n"
         "<script setup lang=\"ts\">\n"
         "function callee(): number { return 42; }\n"
         "function caller(): number { return callee(); }\n"
         "</script>\n"},
    };
    ASSERT_EQ(es_exact_edge_by_name(f, 1, "CALLS", "caller", "callee"), 1);
    PASS();
}

TEST(es_calls_svelte_embedded_issue1807) {
    static const ES_LangFile f[] = {
        {"Toggle.svelte",
         "<script lang=\"ts\">\n"
         "function callee(): number { return 42; }\n"
         "function caller(): number { return callee(); }\n"
         "</script>\n"
         "<button on:click={caller}>Toggle</button>\n"},
    };
    ASSERT_EQ(es_exact_edge_by_name(f, 1, "CALLS", "caller", "callee"), 1);
    PASS();
}

/* Java: caller in Main.java calls static method from Util.java (same package). */
TEST(es_calls_crossfile_java) {
    static const ES_LangFile f[] = {
        {"Util.java",
         "package app;\n\nclass Util {\n    static int square(int x) { return x * x; }\n}\n"},
        {"Main.java",
         "package app;\n\nclass Main {\n    int run(int n) { return Util.square(n); }\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> square */
    PASS();
}

/* Kotlin: caller in Main.kt calls top-level function from Util.kt. */
TEST(es_calls_crossfile_kotlin) {
    static const ES_LangFile f[] = {
        {"Util.kt",
         "fun double(x: Int): Int = x * 2\n"},
        {"Main.kt",
         "fun run(n: Int): Int = double(n)\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* run -> double */
    PASS();
}

/* C#: caller in Main.cs calls static method from Util.cs (same namespace). */
TEST(es_calls_crossfile_csharp) {
    static const ES_LangFile f[] = {
        {"Util.cs",
         "namespace App {\n    class Util {\n"
         "        public static int Square(int x) { return x * x; }\n    }\n}\n"},
        {"Main.cs",
         "namespace App {\n    class Main {\n"
         "        public int Run(int n) { return Util.Square(n); }\n    }\n}\n"}};
    ASSERT_TRUE(es_edge_present(f, 2, "CALLS", 1)); /* Run -> Square */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 2: INHERITS cross-file
 *
 * Subclass in file B extends base class defined in file A.
 * Requires both: (a) correct base_classes extraction AND (b) registry
 * resolving the base name to the correct node.
 *
 * Expected GREEN: Java, C#, C++ (extractors confirmed correct).
 * Expected RED:   Python, TypeScript, PHP, Kotlin (extraction bugs).
 * ══════════════════════════════════════════════════════════════════ */

/* Java cross-file INHERITS — expected GREEN.
 * Animal in Animal.java, Dog extends Animal in Dog.java, same package. */
TEST(es_inherits_crossfile_java) {
    static const ES_LangFile f[] = {
        {"Animal.java",
         "package zoo;\n\nclass Animal {\n    int speak() { return 0; }\n}\n"},
        {"Dog.java",
         "package zoo;\n\nclass Dog extends Animal {\n    int speak() { return 1; }\n}\n"}};
    /* GREEN: Java extraction correct; registry resolves cross-file same-package. */
    ASSERT_TRUE(es_edge_present(f, 2, "INHERITS", 1)); /* Dog -> Animal */
    PASS();
}

/* C# cross-file INHERITS — expected GREEN.
 * Base in Base.cs, Derived extends Base in Derived.cs, same namespace. */
TEST(es_inherits_crossfile_csharp) {
    static const ES_LangFile f[] = {
        {"Base.cs",
         "namespace App {\n    class Base {\n        public int Value() { return 0; }\n    }\n}\n"},
        {"Derived.cs",
         "namespace App {\n    class Derived : Base {\n"
         "        public int Extra() { return 1; }\n    }\n}\n"}};
    /* GREEN: C# extraction confirmed correct. */
    ASSERT_TRUE(es_edge_present(f, 2, "INHERITS", 1)); /* Derived -> Base */
    PASS();
}

/* C++ cross-file INHERITS — expected GREEN.
 * Shape in shape.cpp, Circle extends Shape in circle.cpp. */
TEST(es_inherits_crossfile_cpp) {
    static const ES_LangFile f[] = {
        {"shape.cpp",
         "class Shape {\npublic:\n    virtual int area() { return 0; }\n};\n"},
        {"circle.cpp",
         "class Shape;\n\nclass Circle : public Shape {\npublic:\n"
         "    int area() { return 3; }\n};\n"}};
    /* GREEN: C++ extraction confirmed correct. */
    ASSERT_TRUE(es_edge_present(f, 2, "INHERITS", 1)); /* Circle -> Shape */
    PASS();
}

/* Python cross-file INHERITS — expected RED (extraction bug: base_classes
 * holds "(Animal)" with parens, not "Animal").
 * Reproduction: confirms the end-to-end gap from extraction to graph edge. */
TEST(es_inherits_crossfile_python_red) {
    static const ES_LangFile f[] = {
        {"animal.py",
         "class Animal:\n    def speak(self):\n        return 0\n"},
        {"dog.py",
         "from .animal import Animal\n\n\nclass Dog(Animal):\n    def speak(self):\n        return 1\n"}};
    /* RED: base_classes extraction broken for Python plain identifier nodes.
     * Root cause: collect_bases_from_field does not match bare `identifier`
     * nodes from tree-sitter-python; stores "(Animal)" with parens.
     * Fix location: extract_defs.c collect_bases_from_field / Python case.
     * This test SHOULD FAIL (count=0) until that fix lands. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 2);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "INHERITS") : -1;
    if (got >= 1) {
        fprintf(stderr, "  [ES-EDGE] UNEXPECTED PASS: Python cross-file INHERITS got=%d "
                        "(extraction bug may have been fixed — promote to GREEN)\n", got);
    } else {
        fprintf(stderr, "  [ES-EDGE] CONFIRMED RED: Python cross-file INHERITS got=%d "
                        "(extraction bug reproduces end-to-end)\n", got);
    }
    es_lang_cleanup(&lp, store);
    /* Assert the CORRECT outcome: edge should be present.
     * This FAILS (RED) until the extraction bug is fixed. */
    ASSERT_TRUE(got >= 1);
    PASS();
}

/* TypeScript cross-file INHERITS — expected RED (extractor stores "extends"
 * keyword instead of the base type name). */
TEST(es_inherits_crossfile_typescript_red) {
    static const ES_LangFile f[] = {
        {"base.ts",
         "export class Base {\n    value(): number { return 0; }\n}\n"},
        {"derived.ts",
         "import { Base } from './base';\n\n"
         "export class Derived extends Base {\n    extra(): number { return 1; }\n}\n"}};
    /* RED: TypeScript extractor stores "extends" keyword in base_classes.
     * Root cause: TS extraction walks the heritage_clause and captures the
     * keyword token rather than the type_identifier that follows it.
     * Fix location: extract_defs.c TypeScript heritage clause handling.
     * This test SHOULD FAIL until fixed. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 2);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "INHERITS") : -1;
    if (got >= 1) {
        fprintf(stderr, "  [ES-EDGE] UNEXPECTED PASS: TypeScript cross-file INHERITS got=%d "
                        "(promote to GREEN if extraction fixed)\n", got);
    } else {
        fprintf(stderr, "  [ES-EDGE] CONFIRMED RED: TypeScript cross-file INHERITS got=%d\n", got);
    }
    es_lang_cleanup(&lp, store);
    ASSERT_TRUE(got >= 1); /* FAILS (RED) until TS extraction fixed */
    PASS();
}

/* PHP cross-file INHERITS — expected RED (base_classes never populated). */
TEST(es_inherits_crossfile_php_red) {
    static const ES_LangFile f[] = {
        {"Base.php",
         "<?php\nclass Base {\n    public function value() { return 0; }\n}\n"},
        {"Child.php",
         "<?php\nrequire_once 'Base.php';\n\nclass Child extends Base {\n"
         "    public function extra() { return 1; }\n}\n"}};
    /* RED: PHP extractor does not populate base_classes for `extends`.
     * Fix location: extract_defs.c PHP class heritage clause.
     * FAILS (RED) until fixed. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 2);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "INHERITS") : -1;
    if (got >= 1) {
        fprintf(stderr, "  [ES-EDGE] UNEXPECTED PASS: PHP cross-file INHERITS got=%d "
                        "(promote to GREEN)\n", got);
    } else {
        fprintf(stderr, "  [ES-EDGE] CONFIRMED RED: PHP cross-file INHERITS got=%d\n", got);
    }
    es_lang_cleanup(&lp, store);
    ASSERT_TRUE(got >= 1); /* FAILS (RED) until PHP extraction fixed */
    PASS();
}

/* Kotlin cross-file INHERITS — expected RED (`:` supertype syntax not parsed). */
TEST(es_inherits_crossfile_kotlin_red) {
    static const ES_LangFile f[] = {
        {"Base.kt",
         "open class Base {\n    open fun value(): Int = 0\n}\n"},
        {"Child.kt",
         "class Child : Base() {\n    override fun value(): Int = 1\n}\n"}};
    /* RED: Kotlin extractor does not parse `:` supertype syntax → base_classes empty.
     * Fix location: extract_defs.c Kotlin class body / supertype_list handling.
     * FAILS (RED) until fixed. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 2);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "INHERITS") : -1;
    if (got >= 1) {
        fprintf(stderr, "  [ES-EDGE] UNEXPECTED PASS: Kotlin cross-file INHERITS got=%d "
                        "(promote to GREEN)\n", got);
    } else {
        fprintf(stderr, "  [ES-EDGE] CONFIRMED RED: Kotlin cross-file INHERITS got=%d\n", got);
    }
    es_lang_cleanup(&lp, store);
    ASSERT_TRUE(got >= 1); /* FAILS (RED) until Kotlin extraction fixed */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * TwinCAT: namespace-qualified bases resolve inside their library
 *
 * LibB's .plcproj maps the alias Ns_A to the library LibA. Both libraries
 * define I_Event and FB_Box, so `EXTENDS Ns_A.I_Event` must bind LibA's node
 * and never the same-named one in LibB (a last-segment guess would). The
 * alias is case-insensitive (real projects spell `VND_Util.` next to `Vnd_Util`), an
 * undeclared alias gets no edge, and a qualified base naming the class's own
 * short name (`FB_Box EXTENDS Ns_A.FB_Box`) binds the other library's block.
 * Run below and above MIN_FILES_FOR_PARALLEL: both venues resolve bases.
 * ══════════════════════════════════════════════════════════════════ */

#define ES_TC_PATH 256
#define ES_TC_PAD_FILES 55

static const char ES_TC_POU[] = "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
                                "<TcPlcObject Version=\"1.1.0.1\">\n"
                                "  <POU Name=\"%s\" Id=\"{1}\" SpecialFunc=\"None\">\n"
                                "    <Declaration><![CDATA[%s\n"
                                "VAR\n"
                                "END_VAR\n"
                                "]]></Declaration>\n"
                                "    <Implementation>\n"
                                "      <ST><![CDATA[]]></ST>\n"
                                "    </Implementation>\n"
                                "  </POU>\n"
                                "</TcPlcObject>\n";

static const char ES_TC_ITF[] = "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
                                "<TcPlcObject Version=\"1.1.0.1\">\n"
                                "  <Itf Name=\"%s\" Id=\"{1}\">\n"
                                "    <Declaration><![CDATA[%s\n"
                                "]]></Declaration>\n"
                                "    <Method Name=\"Fire\" Id=\"{2}\">\n"
                                "      <Declaration><![CDATA[METHOD Fire : BOOL\n"
                                "]]></Declaration>\n"
                                "    </Method>\n"
                                "  </Itf>\n"
                                "</TcPlcObject>\n";

static const char ES_TC_LIBA_PROJ[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
    "<Project DefaultTargets=\"Build\" "
    "xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">\n"
    "  <PropertyGroup>\n"
    "    <Name>LibA</Name>\n"
    "    <Title>LibA</Title>\n"
    "    <DefaultNamespace>Ns_A</DefaultNamespace>\n"
    "  </PropertyGroup>\n"
    "</Project>\n";

static const char ES_TC_LIBB_PROJ[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
    "<Project DefaultTargets=\"Build\" "
    "xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">\n"
    "  <PropertyGroup>\n"
    "    <Name>LibB</Name>\n"
    "    <Title>LibB</Title>\n"
    "    <DefaultNamespace>Ns_B</DefaultNamespace>\n"
    "  </PropertyGroup>\n"
    "  <ItemGroup>\n"
    "    <PlaceholderReference Include=\"LibA\">\n"
    "      <DefaultResolution>LibA, * (Vendor)</DefaultResolution>\n"
    "      <Namespace>Ns_A</Namespace>\n"
    "      <QualifiedOnly>true</QualifiedOnly>\n"
    "    </PlaceholderReference>\n"
    "  </ItemGroup>\n"
    "  <ItemGroup>\n"
    "    <PlaceholderResolution Include=\"LibA\">\n"
    "      <Resolution>LibA, 1.0.0.0 (Vendor)</Resolution>\n"
    "    </PlaceholderResolution>\n"
    "  </ItemGroup>\n"
    "</Project>\n";

/* Target file paths of the `edge_type` edges leaving the node `name` defined in
 * `file`. Returns the edge count, or -1 when that source node is not found. */
static int es_tc_edge_targets(cbm_store_t *store, const char *project, const char *name,
                              const char *file, const char *edge_type, char out[][ES_TC_PATH],
                              int max) {
    cbm_node_t *nodes = NULL;
    int count = 0;
    int64_t source_id = 0;
    if (cbm_store_find_nodes_by_name(store, project, name, &nodes, &count) != CBM_STORE_OK) {
        return -1;
    }
    for (int i = 0; i < count; i++) {
        if (nodes[i].file_path && strcmp(nodes[i].file_path, file) == 0) {
            source_id = nodes[i].id;
        }
    }
    cbm_store_free_nodes(nodes, count);
    if (source_id == 0) {
        return -1;
    }
    cbm_edge_t *edges = NULL;
    int edge_count = 0;
    if (cbm_store_find_edges_by_source_type(store, source_id, edge_type, &edges, &edge_count) !=
        CBM_STORE_OK) {
        return -1;
    }
    for (int i = 0; i < edge_count && i < max; i++) {
        cbm_node_t target;
        memset(&target, 0, sizeof(target));
        out[i][0] = '\0';
        if (cbm_store_find_node_by_id(store, edges[i].target_id, &target) == CBM_STORE_OK) {
            snprintf(out[i], ES_TC_PATH, "%s", target.file_path ? target.file_path : "");
            cbm_node_free_fields(&target);
        }
    }
    cbm_store_free_edges(edges, edge_count);
    return edge_count;
}

/* Expect exactly one `edge_type` edge from (name, file), landing in target_file.
 * target_file NULL = expect none. Prints what was found on a mismatch. */
static int es_tc_expect(cbm_store_t *store, const char *project, const char *name, const char *file,
                        const char *edge_type, const char *target_file) {
    char targets[8][ES_TC_PATH];
    int n = es_tc_edge_targets(store, project, name, file, edge_type, targets, 8);
    int ok = target_file ? (n == 1 && strcmp(targets[0], target_file) == 0) : (n == 0);
    if (!ok) {
        fprintf(stderr, "  [ES-TC] FAIL %s (%s) %s: got %d edge(s)", name, file, edge_type, n);
        for (int i = 0; i < n && i < 8; i++) {
            fprintf(stderr, " -> %s", targets[i]);
        }
        fprintf(stderr, ", expected %s\n", target_file ? target_file : "none");
    }
    return ok;
}

/* Source node id of `name` defined in `file`, or 0 when not found. Shared by
 * the strategy-property checks below (es_tc_edge_targets duplicates this
 * lookup instead of calling out to it — kept separate to avoid touching that
 * already-covered helper). */
static int64_t es_tc_source_id(cbm_store_t *store, const char *project, const char *name,
                               const char *file) {
    cbm_node_t *nodes = NULL;
    int count = 0;
    int64_t source_id = 0;
    if (cbm_store_find_nodes_by_name(store, project, name, &nodes, &count) != CBM_STORE_OK) {
        return 0;
    }
    for (int i = 0; i < count; i++) {
        if (nodes[i].file_path && strcmp(nodes[i].file_path, file) == 0) {
            source_id = nodes[i].id;
        }
    }
    cbm_store_free_nodes(nodes, count);
    return source_id;
}

/* Expect exactly one `edge_type` edge from (name, file) whose "strategy"
 * property equals want_strategy (edge properties JSON, e.g.
 * {"...,"strategy":"st_receiver_type",...}). Proves the FOUND branch of
 * cbm_st_resolve_call actually fired, rather than a same-name guess that
 * happens to land on the right target by accident. */
static bool es_tc_expect_strategy(cbm_store_t *store, const char *project, const char *name,
                                  const char *file, const char *edge_type,
                                  const char *want_strategy) {
    int64_t source_id = es_tc_source_id(store, project, name, file);
    if (source_id == 0) {
        fprintf(stderr, "  [ES-TC] FAIL %s (%s) %s strategy: source node not found\n", name, file,
                edge_type);
        return false;
    }
    cbm_edge_t *edges = NULL;
    int edge_count = 0;
    if (cbm_store_find_edges_by_source_type(store, source_id, edge_type, &edges, &edge_count) !=
        CBM_STORE_OK) {
        return false;
    }
    bool ok = false;
    if (edge_count == 1) {
        char needle[ES_TC_PATH];
        snprintf(needle, sizeof(needle), "\"strategy\":\"%s\"", want_strategy);
        ok = edges[0].properties_json && strstr(edges[0].properties_json, needle) != NULL;
        if (!ok) {
            fprintf(stderr, "  [ES-TC] FAIL %s (%s) %s strategy: got %s, want \"%s\"\n", name, file,
                    edge_type, edges[0].properties_json ? edges[0].properties_json : "(null)",
                    want_strategy);
        }
    } else {
        fprintf(stderr, "  [ES-TC] FAIL %s (%s) %s strategy: got %d edge(s), want exactly 1\n",
                name, file, edge_type, edge_count);
    }
    cbm_store_free_edges(edges, edge_count);
    return ok;
}

/* Expect at least one `edge_type` edge from (name, file), none of them
 * carrying want_strategy — the UNTYPED-fall-through counterpart of
 * es_tc_expect_strategy: proves the generic resolver is still reachable when
 * the receiver's declared type does not resolve at all. */
static bool es_tc_expect_none_with_strategy(cbm_store_t *store, const char *project,
                                            const char *name, const char *file,
                                            const char *edge_type, const char *avoid_strategy) {
    int64_t source_id = es_tc_source_id(store, project, name, file);
    if (source_id == 0) {
        fprintf(stderr, "  [ES-TC] FAIL %s (%s) %s strategy: source node not found\n", name, file,
                edge_type);
        return false;
    }
    cbm_edge_t *edges = NULL;
    int edge_count = 0;
    if (cbm_store_find_edges_by_source_type(store, source_id, edge_type, &edges, &edge_count) !=
        CBM_STORE_OK) {
        return false;
    }
    char needle[ES_TC_PATH];
    snprintf(needle, sizeof(needle), "\"strategy\":\"%s\"", avoid_strategy);
    bool ok = edge_count >= 1;
    for (int i = 0; ok && i < edge_count; i++) {
        if (edges[i].properties_json && strstr(edges[i].properties_json, needle)) {
            ok = false;
        }
    }
    if (!ok) {
        fprintf(stderr,
                "  [ES-TC] FAIL %s (%s) %s strategy: got %d edge(s), want >=1 without \"%s\"\n",
                name, file, edge_type, edge_count, avoid_strategy);
    }
    cbm_store_free_edges(edges, edge_count);
    return ok;
}

/* Index the two-library fixture (padded past the parallel threshold when asked)
 * and return the number of failed expectations. */
static int es_tc_namespace_fixture(bool parallel) {
    static char names[ES_TC_PAD_FILES + 8][ES_TC_PATH];
    static char bodies[ES_TC_PAD_FILES + 8][1024];
    ES_LangFile files[ES_TC_PAD_FILES + 8];
    int n = 0;
    struct {
        const char *path;
        const char *tmpl;
        const char *name;
        const char *header;
    } core[] = {
        {"LibA/POUs/I_Event.TcIO", ES_TC_ITF, "I_Event", "INTERFACE I_Event"},
        {"LibA/POUs/FB_Box.TcPOU", ES_TC_POU, "FB_Box", "FUNCTION_BLOCK FB_Box"},
        {"LibB/POUs/I_Event.TcIO", ES_TC_ITF, "I_Event", "INTERFACE I_Event"},
        {"LibB/POUs/I_Spec.TcIO", ES_TC_ITF, "I_Spec", "INTERFACE I_Spec EXTENDS Ns_A.I_Event"},
        {"LibB/POUs/FB_Box.TcPOU", ES_TC_POU, "FB_Box",
         "FUNCTION_BLOCK FB_Box EXTENDS NS_a.FB_Box"},
        {"LibB/POUs/FB_Other.TcPOU", ES_TC_POU, "FB_Other",
         "FUNCTION_BLOCK FB_Other IMPLEMENTS Nope.I_Event, I_Spec"},
    };
    files[n++] = (ES_LangFile){"LibA/LibA.plcproj", ES_TC_LIBA_PROJ};
    files[n++] = (ES_LangFile){"LibB/LibB.plcproj", ES_TC_LIBB_PROJ};
    for (size_t i = 0; i < sizeof(core) / sizeof(core[0]); i++) {
        snprintf(bodies[n], sizeof(bodies[n]), core[i].tmpl, core[i].name, core[i].header);
        files[n] = (ES_LangFile){core[i].path, bodies[n]};
        n++;
    }
    for (int i = 0; parallel && i < ES_TC_PAD_FILES; i++) {
        char pad[32];
        char header[64];
        snprintf(pad, sizeof(pad), "FB_Pad%02d", i);
        snprintf(header, sizeof(header), "FUNCTION_BLOCK %s", pad);
        snprintf(names[n], sizeof(names[n]), "LibB/Pad/%s.TcPOU", pad);
        snprintf(bodies[n], sizeof(bodies[n]), ES_TC_POU, pad, header);
        files[n] = (ES_LangFile){names[n], bodies[n]};
        n++;
    }

    const char *old_workers = getenv("CBM_WORKERS");
    char *saved_workers = old_workers ? strdup(old_workers) : NULL;
    if (parallel) {
        cbm_setenv("CBM_WORKERS", "4", 1);
    }
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, files, n);
    if (parallel) {
        if (saved_workers) {
            cbm_setenv("CBM_WORKERS", saved_workers, 1);
        } else {
            cbm_unsetenv("CBM_WORKERS");
        }
    }
    free(saved_workers);
    if (!store) {
        es_lang_cleanup(&lp, store);
        return 1;
    }

    const char *p = lp.project;
    int failed = 0;
    /* Binds LibA's I_Event, not LibB's own same-named interface. */
    failed += !es_tc_expect(store, p, "I_Spec", "LibB/POUs/I_Spec.TcIO", "IMPLEMENTS",
                            "LibA/POUs/I_Event.TcIO");
    /* Case-insensitive alias; the same short name as the class itself. */
    failed += !es_tc_expect(store, p, "FB_Box", "LibB/POUs/FB_Box.TcPOU", "INHERITS",
                            "LibA/POUs/FB_Box.TcPOU");
    failed += !es_tc_expect(store, p, "FB_Box", "LibA/POUs/FB_Box.TcPOU", "INHERITS", NULL);
    /* Undeclared alias: no edge; the unqualified base next to it still binds. */
    failed += !es_tc_expect(store, p, "FB_Other", "LibB/POUs/FB_Other.TcPOU", "IMPLEMENTS",
                            "LibB/POUs/I_Spec.TcIO");
    if (failed) {
        es_dump_edge_histogram(store, p);
    }
    es_lang_cleanup(&lp, store);
    return failed;
}

TEST(es_twincat_qualified_base_in_library_sequential) {
    ASSERT_TRUE(es_tc_namespace_fixture(false) == 0);
    PASS();
}

TEST(es_twincat_qualified_base_in_library_parallel) {
    ASSERT_TRUE(es_tc_namespace_fixture(true) == 0);
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * TwinCAT DUT internals: enum members / struct fields as Field nodes,
 * member-level USAGE edges, and line/count occurrence data on USAGE.
 *
 * Two libraries: LibM (namespace Ns_M, holds E_Alarm + I_ParInt) and LibApp,
 * which references LibM and holds the DUTs and FB_Drain. Line numbers in the
 * literals below are the XML lines the assertions compare against.
 * ══════════════════════════════════════════════════════════════════ */

static const char ES_TC_DUT[] = "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
                                "<TcPlcObject Version=\"1.1.0.1\">\n"
                                "  <DUT Name=\"%s\" Id=\"{1}\">\n"
                                "    <Declaration><![CDATA[%s]]></Declaration>\n"
                                "  </DUT>\n"
                                "</TcPlcObject>\n";

/* Declaration text starts on XML line 4. */
static const char ES_TC_ENUM_DECL[] = "{attribute 'qualified_only'}\n"    /* 4 */
                                      "{attribute 'strict'}\n"            /* 5 */
                                      "TYPE E_ValveState :\n"             /* 6 */
                                      "(\n"                               /* 7 */
                                      "\tONE_TIME_INIT := 0,\n"           /* 8 */
                                      "\tINIT,\n"                         /* 9 */
                                      "\t(* comment between members *)\n" /* 10 */
                                      "\tOPEN := 2,\n"                    /* 11 */
                                      "\tCLOSE,\n"                        /* 12 */
                                      "\tERROR_LIMIT := 10\n"             /* 13 */
                                      ") UINT;\n"                         /* 14 */
                                      "END_TYPE\n";                       /* 15 */

static const char ES_TC_STRUCT_DECL[] = "TYPE T_Par :\n"                      /* 4 */
                                        "STRUCT\n"                            /* 5 */
                                        "\tNumberOfPulses : Ns_M.I_ParInt;\n" /* 6 */
                                        "\tPulsesOnTime : Ns_M.I_ParInt;\n"   /* 7 */
                                        "\tInner : T_Inner;\n"                /* 8 */
                                        "\tArr : ARRAY [0..3] OF INT;\n"      /* 9 */
                                        "END_STRUCT\n"                        /* 10 */
                                        "END_TYPE\n";                         /* 11 */

static const char ES_TC_INNER_DECL[] = "TYPE T_Inner :\n"
                                       "STRUCT\n"
                                       "\tDepth : INT;\n"
                                       "END_STRUCT\n"
                                       "END_TYPE\n";

static const char ES_TC_UNION_DECL[] = "TYPE U_Raw :\n"
                                       "UNION\n"
                                       "\tWord : WORD;\n"
                                       "\tBytes : ARRAY [0..1] OF BYTE;\n"
                                       "END_UNION\n"
                                       "END_TYPE\n";

static const char ES_TC_ALARM_DECL[] = "{attribute 'qualified_only'}\n"
                                       "TYPE E_Alarm :\n"
                                       "(\n"
                                       "\tOFF := 0,\n"
                                       "\tACTIVE\n"
                                       ") UINT;\n"
                                       "END_TYPE\n";

static const char ES_TC_FB_DRAIN[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"                /* 1 */
    "<TcPlcObject Version=\"1.1.0.1\">\n"                         /* 2 */
    "  <POU Name=\"FB_Drain\" Id=\"{1}\" SpecialFunc=\"None\">\n" /* 3 */
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Drain\n"         /* 4 */
    "VAR_INPUT\n"                                                 /* 5 */
    "\tinPar : T_Par;\n"                                          /* 6 */
    "END_VAR\n"                                                   /* 7 */
    "VAR\n"                                                       /* 8 */
    "\t_state : E_ValveState;\n"                                  /* 9 */
    "\t_par : T_Par;\n"                                           /* 10 */
    "END_VAR\n"                                                   /* 11 */
    "]]></Declaration>\n"                                         /* 12 */
    "    <Implementation>\n"                                      /* 13 */
    "      <ST><![CDATA[stateMachine();]]></ST>\n"                /* 14 */
    "    </Implementation>\n"                                     /* 15 */
    "    <Method Name=\"stateMachine\" Id=\"{2}\">\n"             /* 16 */
    "      <Declaration><![CDATA[METHOD stateMachine : BOOL\n"    /* 17 */
    "VAR\n"                                                       /* 18 */
    "\tlocal : T_Inner;\n"                                        /* 19 */
    "\talarm : Ns_M.E_Alarm;\n"                                   /* 20 */
    "\tx : INT;\n"                                                /* 21 */
    "\ty : INT;\n"                                                /* 22 */
    "END_VAR\n"                                                   /* 23 */
    "]]></Declaration>\n"                                         /* 24 */
    "      <Implementation>\n"                                    /* 25 */
    "        <ST><![CDATA[CASE _state OF\n"                       /* 26 */
    "\tE_ValveState.OPEN:\n"                                      /* 27 */
    "\t\t_par.NumberOfPulses.Value := 1;\n"                       /* 28 */
    "\t\tIF inPar.Inner.Depth > 0 THEN\n"                         /* 29 */
    "\t\t\tlocal.Depth := 2;\n"                                   /* 30 */
    "\t\tEND_IF\n"                                                /* 31 */
    "\tE_ValveState.CLOSE:\n"                                     /* 32 */
    "\t\t_state := E_ValveState.CLOSE;\n"                         /* 33 */
    "END_CASE\n"                                                  /* 34 */
    "IF _state = E_ValveState.CLOSE THEN\n"                       /* 35 */
    "\talarm := Ns_M.E_Alarm.OFF;\n"                              /* 36 */
    "\tx := E_ValveState.UNKNOWN_MEMBER;\n"                       /* 37 */
    "\ty := CLOSE;\n"                                             /* 38 */
    "END_IF]]></ST>\n"                                            /* 39 */
    "      </Implementation>\n"                                   /* 40 */
    "    </Method>\n"                                             /* 41 */
    "    <Method Name=\"Test_Close\" Id=\"{3}\">\n"               /* 42 */
    "      <Declaration><![CDATA[METHOD Test_Close : BOOL\n"      /* 43 */
    "]]></Declaration>\n"                                         /* 44 */
    "      <Implementation>\n"                                    /* 45 */
    "        <ST><![CDATA[AssertEquals_UINT(Expected := E_ValveState.CLOSE, Actual := "
    "_state);]]></ST>\n"        /* 46 */
    "      </Implementation>\n" /* 47 */
    "    </Method>\n"           /* 48 */
    "  </POU>\n"                /* 49 */
    "</TcPlcObject>\n";         /* 50 */

static const char ES_TC_LIBM_PROJ[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
    "<Project DefaultTargets=\"Build\" "
    "xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">\n"
    "  <PropertyGroup>\n"
    "    <Name>LibM</Name>\n"
    "    <Title>LibM</Title>\n"
    "    <DefaultNamespace>Ns_M</DefaultNamespace>\n"
    "  </PropertyGroup>\n"
    "</Project>\n";

static const char ES_TC_LIBAPP_PROJ[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
    "<Project DefaultTargets=\"Build\" "
    "xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">\n"
    "  <PropertyGroup>\n"
    "    <Name>LibApp</Name>\n"
    "    <Title>LibApp</Title>\n"
    "  </PropertyGroup>\n"
    "  <ItemGroup>\n"
    "    <PlaceholderReference Include=\"LibM\">\n"
    "      <DefaultResolution>LibM, * (Vendor)</DefaultResolution>\n"
    "      <Namespace>Ns_M</Namespace>\n"
    "    </PlaceholderReference>\n"
    "  </ItemGroup>\n"
    "</Project>\n";

/* A same-named enum in the OTHER library: `E_ValveState.CLOSE` in LibApp must
 * bind LibApp's enum and never this one, and the bare name CLOSE becomes
 * ambiguous project-wide (as it is in real projects). */
static const char ES_TC_DUP_ENUM_DECL[] = "{attribute 'qualified_only'}\n"
                                          "TYPE E_ValveState :\n"
                                          "(\n"
                                          "\tOPEN := 20,\n"
                                          "\tCLOSE := 21\n"
                                          ") UINT;\n"
                                          "END_TYPE\n";

/* Cross-language decoy: the only type named T_Foreign is a C struct. An ST
 * variable of that (undeclared in ST) type must resolve no member. */
static const char ES_TC_FOREIGN_C[] = "struct T_Foreign {\n    int Depth;\n};\n";

static const char ES_TC_FB_FOREIGN[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
    "<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_Foreign\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Foreign\n"
    "VAR\n"
    "\tforeign : T_Foreign;\n"
    "END_VAR\n"
    "]]></Declaration>\n"
    "    <Implementation>\n"
    "      <ST><![CDATA[foreign.Depth := 1;]]></ST>\n"
    "    </Implementation>\n"
    "  </POU>\n"
    "</TcPlcObject>\n";

/* Same-file preference: two plain .st files in one library both declare T_Loc;
 * a reference in a.st binds a.st's T_Loc, never b.st's. */
static const char ES_TC_PLAIN_A[] = "TYPE T_Loc : STRUCT Depth : INT; END_STRUCT END_TYPE\n"
                                    "FUNCTION_BLOCK FB_Loc\n"
                                    "VAR\n"
                                    "\tv : T_Loc;\n"
                                    "END_VAR\n"
                                    "v.Depth := 1;\n"
                                    "END_FUNCTION_BLOCK\n";
static const char ES_TC_PLAIN_B[] = "TYPE T_Loc : STRUCT Depth : INT; END_STRUCT END_TYPE\n";

#define ES_TCM_FILES (14 + ES_TC_PAD_FILES)
#define ES_TCM_SET_MAX 64
#define ES_TCM_ENTRY 256

typedef struct {
    char names[ES_TCM_FILES][ES_TC_PATH];
    char bodies[ES_TCM_FILES][2048];
    ES_LangFile files[ES_TCM_FILES];
    int n;
} ES_TcMemberFixture;

/* Build the DUT-internals fixture; padded past the parallel threshold when asked. */
static void es_tcm_build(ES_TcMemberFixture *fx, bool parallel, bool dup_enum) {
    fx->n = 0;
    if (dup_enum) {
        snprintf(fx->bodies[fx->n], sizeof(fx->bodies[fx->n]), ES_TC_DUT, "E_ValveState",
                 ES_TC_DUP_ENUM_DECL);
        fx->files[fx->n] = (ES_LangFile){"LibM/DUTs/E_ValveState.TcDUT", fx->bodies[fx->n]};
        fx->n++;
        fx->files[fx->n++] = (ES_LangFile){"LibApp/native/foreign.c", ES_TC_FOREIGN_C};
        fx->files[fx->n++] = (ES_LangFile){"LibApp/POUs/FB_Foreign.TcPOU", ES_TC_FB_FOREIGN};
        fx->files[fx->n++] = (ES_LangFile){"LibApp/Plain/a.st", ES_TC_PLAIN_A};
        fx->files[fx->n++] = (ES_LangFile){"LibApp/Plain/b.st", ES_TC_PLAIN_B};
    }
    struct {
        const char *path;
        const char *name;
        const char *decl;
    } duts[] = {
        {"LibApp/DUTs/E_ValveState.TcDUT", "E_ValveState", ES_TC_ENUM_DECL},
        {"LibApp/DUTs/T_Par.TcDUT", "T_Par", ES_TC_STRUCT_DECL},
        {"LibApp/DUTs/T_Inner.TcDUT", "T_Inner", ES_TC_INNER_DECL},
        {"LibApp/DUTs/U_Raw.TcDUT", "U_Raw", ES_TC_UNION_DECL},
        {"LibM/DUTs/E_Alarm.TcDUT", "E_Alarm", ES_TC_ALARM_DECL},
    };
    fx->files[fx->n++] = (ES_LangFile){"LibM/LibM.plcproj", ES_TC_LIBM_PROJ};
    fx->files[fx->n++] = (ES_LangFile){"LibApp/LibApp.plcproj", ES_TC_LIBAPP_PROJ};
    for (size_t i = 0; i < sizeof(duts) / sizeof(duts[0]); i++) {
        snprintf(fx->bodies[fx->n], sizeof(fx->bodies[fx->n]), ES_TC_DUT, duts[i].name,
                 duts[i].decl);
        fx->files[fx->n] = (ES_LangFile){duts[i].path, fx->bodies[fx->n]};
        fx->n++;
    }
    snprintf(fx->bodies[fx->n], sizeof(fx->bodies[fx->n]), ES_TC_ITF, "I_ParInt",
             "INTERFACE I_ParInt");
    fx->files[fx->n] = (ES_LangFile){"LibM/POUs/I_ParInt.TcIO", fx->bodies[fx->n]};
    fx->n++;
    fx->files[fx->n++] = (ES_LangFile){"LibApp/POUs/FB_Drain.TcPOU", ES_TC_FB_DRAIN};
    for (int i = 0; parallel && i < ES_TC_PAD_FILES; i++) {
        char pad[32];
        char header[64];
        snprintf(pad, sizeof(pad), "FB_Pad%02d", i);
        snprintf(header, sizeof(header), "FUNCTION_BLOCK %s", pad);
        snprintf(fx->names[fx->n], ES_TC_PATH, "LibApp/Pad/%s.TcPOU", pad);
        snprintf(fx->bodies[fx->n], sizeof(fx->bodies[fx->n]), ES_TC_POU, pad, header);
        fx->files[fx->n] = (ES_LangFile){fx->names[fx->n], fx->bodies[fx->n]};
        fx->n++;
    }
}

static cbm_store_t *es_tcm_index(ES_LangProj *lp, ES_TcMemberFixture *fx, bool parallel,
                                 bool dup_enum) {
    es_tcm_build(fx, parallel, dup_enum);
    const char *old_workers = getenv("CBM_WORKERS");
    char *saved_workers = old_workers ? strdup(old_workers) : NULL;
    if (parallel) {
        cbm_setenv("CBM_WORKERS", "4", 1);
    }
    cbm_store_t *store = es_lang_index_files(lp, fx->files, fx->n);
    if (parallel) {
        if (saved_workers) {
            cbm_setenv("CBM_WORKERS", saved_workers, 1);
        } else {
            cbm_unsetenv("CBM_WORKERS");
        }
    }
    free(saved_workers);
    return store;
}

static int es_tcm_cmp_str(const void *a, const void *b) {
    return strcmp((const char *)a, (const char *)b);
}

/* Every USAGE edge landing on a Type node, as sorted "src_label src_name@src_file -> target"
 * entries. Returns the entry count, or -1 on a store error. */
static int es_tcm_type_usage_set(cbm_store_t *store, const char *project, char out[][ES_TCM_ENTRY],
                                 int max) {
    cbm_edge_t *edges = NULL;
    int count = 0;
    if (cbm_store_find_edges_by_type(store, project, "USAGE", &edges, &count) != CBM_STORE_OK) {
        return -1;
    }
    int n = 0;
    for (int i = 0; i < count && n < max; i++) {
        cbm_node_t src;
        cbm_node_t tgt;
        memset(&src, 0, sizeof(src));
        memset(&tgt, 0, sizeof(tgt));
        if (cbm_store_find_node_by_id(store, edges[i].target_id, &tgt) != CBM_STORE_OK) {
            continue;
        }
        if (tgt.label && strcmp(tgt.label, "Type") == 0 &&
            cbm_store_find_node_by_id(store, edges[i].source_id, &src) == CBM_STORE_OK) {
            snprintf(out[n++], ES_TCM_ENTRY, "%s %s@%s -> %s", src.label, src.name, src.file_path,
                     tgt.name);
            cbm_node_free_fields(&src);
        }
        cbm_node_free_fields(&tgt);
    }
    cbm_store_free_edges(edges, count);
    qsort(out, (size_t)n, ES_TCM_ENTRY, es_tcm_cmp_str);
    return n;
}

/* Regression guard: the type-level USAGE edge set of the fixture, snapshotted
 * from the build BEFORE DUT internals became nodes. Member-level edges land on
 * Field nodes and are therefore invisible here by construction. */
TEST(es_twincat_type_usage_edge_set_unchanged) {
    ES_LangProj lp;
    ES_TcMemberFixture *fx = calloc(1, sizeof(*fx));
    ASSERT_NOT_NULL(fx);
    cbm_store_t *store = es_tcm_index(&lp, fx, false, false);
    ASSERT_NOT_NULL(store);
    static char got[ES_TCM_SET_MAX][ES_TCM_ENTRY];
    int n = es_tcm_type_usage_set(store, lp.project, got, ES_TCM_SET_MAX);
    es_lang_cleanup(&lp, store);
    free(fx);
    /* Snapshot taken 2026-09-16 from the pre-change build (sorted). */
    static const char *const EXPECTED[] = {
        "Method Test_Close@LibApp/POUs/FB_Drain.TcPOU -> E_ValveState",
        "Method stateMachine@LibApp/POUs/FB_Drain.TcPOU -> E_Alarm",
        "Method stateMachine@LibApp/POUs/FB_Drain.TcPOU -> E_ValveState",
        "Method stateMachine@LibApp/POUs/FB_Drain.TcPOU -> T_Inner",
        "Module LibApp/DUTs/T_Par.TcDUT@LibApp/DUTs/T_Par.TcDUT -> T_Inner",
        "Module LibApp/POUs/FB_Drain.TcPOU@LibApp/POUs/FB_Drain.TcPOU -> E_ValveState",
        "Module LibApp/POUs/FB_Drain.TcPOU@LibApp/POUs/FB_Drain.TcPOU -> T_Par",
    };
    const int expected_n = (int)(sizeof(EXPECTED) / sizeof(EXPECTED[0]));
    int mismatch = n != expected_n;
    for (int i = 0; i < n && i < expected_n; i++) {
        mismatch |= strcmp(got[i], EXPECTED[i]) != 0;
    }
    if (mismatch) {
        fprintf(stderr, "  [ES-TCM] type-level USAGE set changed (%d entries, expected %d):\n", n,
                expected_n);
        for (int i = 0; i < n; i++) {
            fprintf(stderr, "    got:      %s\n", got[i]);
        }
    }
    ASSERT_FALSE(mismatch);
    PASS();
}

/* The node `name` with `label` defined in `file`; 0 when absent or ambiguous. */
static int64_t es_tcm_node_id(cbm_store_t *store, const char *project, const char *label,
                              const char *name, const char *file) {
    cbm_node_t *nodes = NULL;
    int count = 0;
    int64_t id = 0;
    int hits = 0;
    if (cbm_store_find_nodes_by_name(store, project, name, &nodes, &count) != CBM_STORE_OK) {
        return 0;
    }
    for (int i = 0; i < count; i++) {
        if (nodes[i].label && strcmp(nodes[i].label, label) == 0 && nodes[i].file_path &&
            strcmp(nodes[i].file_path, file) == 0) {
            id = nodes[i].id;
            hits++;
        }
    }
    cbm_store_free_nodes(nodes, count);
    return hits == 1 ? id : 0;
}

/* Copy the properties JSON of the one `type` edge src -> tgt into `out`.
 * Returns 1 when exactly one such edge exists, 0 when none, -1 when several. */
static int es_tcm_edge_props(cbm_store_t *store, int64_t src, int64_t tgt, const char *type,
                             char *out, size_t out_size) {
    cbm_edge_t *edges = NULL;
    int count = 0;
    int hits = 0;
    out[0] = '\0';
    if (src == 0 || tgt == 0 ||
        cbm_store_find_edges_by_source_type(store, src, type, &edges, &count) != CBM_STORE_OK) {
        return 0;
    }
    for (int i = 0; i < count; i++) {
        if (edges[i].target_id == tgt) {
            snprintf(out, out_size, "%s",
                     edges[i].properties_json ? edges[i].properties_json : "{}");
            hits++;
        }
    }
    cbm_store_free_edges(edges, count);
    return hits > 1 ? -1 : hits;
}

/* Number of `type` edges landing on `tgt`. */
static int es_tcm_inbound(cbm_store_t *store, int64_t tgt, const char *type) {
    cbm_edge_t *edges = NULL;
    int count = 0;
    if (tgt == 0 ||
        cbm_store_find_edges_by_target_type(store, tgt, type, &edges, &count) != CBM_STORE_OK) {
        return -1;
    }
    cbm_store_free_edges(edges, count);
    return count;
}

/* Expect one USAGE edge src -> tgt whose properties carry the given line and count. */
static int es_tcm_expect_usage(cbm_store_t *store, int64_t src, int64_t tgt, const char *what,
                               int line, int count) {
    char props[512];
    char want_line[32];
    char want_count[32];
    int n = es_tcm_edge_props(store, src, tgt, "USAGE", props, sizeof(props));
    snprintf(want_line, sizeof(want_line), "\"line\":%d", line);
    snprintf(want_count, sizeof(want_count), "\"count\":%d", count);
    int ok = n == 1 && strstr(props, want_line) && strstr(props, want_count);
    if (!ok) {
        fprintf(stderr, "  [ES-TCM] USAGE %s: edges=%d props=%s (want line %d, count %d)\n", what,
                n, props, line, count);
    }
    return ok;
}

#define ES_TCM_ENUM_FILE "LibApp/DUTs/E_ValveState.TcDUT"
#define ES_TCM_PAR_FILE "LibApp/DUTs/T_Par.TcDUT"
#define ES_TCM_INNER_FILE "LibApp/DUTs/T_Inner.TcDUT"
#define ES_TCM_UNION_FILE "LibApp/DUTs/U_Raw.TcDUT"
#define ES_TCM_ALARM_FILE "LibM/DUTs/E_Alarm.TcDUT"
#define ES_TCM_FB_FILE "LibApp/POUs/FB_Drain.TcPOU"

/* Enum members, struct fields and union members are Field nodes under their
 * Type (DEFINES), with enum_value / return_type / parent_class properties. */
TEST(es_twincat_dut_members_are_fields_under_type) {
    ES_LangProj lp;
    ES_TcMemberFixture *fx = calloc(1, sizeof(*fx));
    ASSERT_NOT_NULL(fx);
    cbm_store_t *store = es_tcm_index(&lp, fx, false, false);
    ASSERT_NOT_NULL(store);
    int failed = 0;

    int64_t enum_id = es_tcm_node_id(store, lp.project, "Type", "E_ValveState", ES_TCM_ENUM_FILE);
    failed += enum_id == 0;
    struct {
        const char *name;
        const char *value;
        int line;
    } members[] = {{"ONE_TIME_INIT", "\"enum_value\":0", 8},
                   {"INIT", "\"enum_value\":1", 9},
                   {"OPEN", "\"enum_value\":2", 11},
                   {"CLOSE", "\"enum_value\":3", 12},
                   {"ERROR_LIMIT", "\"enum_value\":10", 13}};
    for (size_t i = 0; i < sizeof(members) / sizeof(members[0]); i++) {
        int64_t fid = es_tcm_node_id(store, lp.project, "Field", members[i].name, ES_TCM_ENUM_FILE);
        cbm_node_t f;
        memset(&f, 0, sizeof(f));
        int ok = fid != 0 && cbm_store_find_node_by_id(store, fid, &f) == CBM_STORE_OK;
        if (ok) {
            char parent[512];
            cbm_node_t t;
            memset(&t, 0, sizeof(t));
            cbm_store_find_node_by_id(store, enum_id, &t);
            snprintf(parent, sizeof(parent), "\"parent_class\":\"%s\"",
                     t.qualified_name ? t.qualified_name : "?");
            ok = f.properties_json && strstr(f.properties_json, members[i].value) &&
                 strstr(f.properties_json, "\"return_type\":\"UINT\"") &&
                 strstr(f.properties_json, parent) && f.start_line == members[i].line;
            if (!ok) {
                fprintf(stderr, "  [ES-TCM] Field %s: line=%d props=%s\n", members[i].name,
                        f.start_line, f.properties_json ? f.properties_json : "(null)");
            }
            char props[64];
            int e = es_tcm_edge_props(store, enum_id, fid, "DEFINES", props, sizeof(props));
            if (e != 1) {
                fprintf(stderr, "  [ES-TCM] Type -DEFINES-> %s: %d edge(s)\n", members[i].name, e);
                ok = 0;
            }
            cbm_node_free_fields(&t);
            cbm_node_free_fields(&f);
        } else {
            fprintf(stderr, "  [ES-TCM] Field %s missing\n", members[i].name);
        }
        failed += !ok;
    }
    /* Exactly the five members hang off the enum. */
    cbm_edge_t *edges = NULL;
    int ecount = 0;
    if (cbm_store_find_edges_by_source_type(store, enum_id, "DEFINES", &edges, &ecount) ==
        CBM_STORE_OK) {
        if (ecount != 5) {
            fprintf(stderr, "  [ES-TCM] enum DEFINES out-degree %d, expected 5\n", ecount);
            failed++;
        }
        cbm_store_free_edges(edges, ecount);
    }

    /* Struct: declared type text incl. the library prefix, no enum_value. */
    int64_t par_id = es_tcm_node_id(store, lp.project, "Type", "T_Par", ES_TCM_PAR_FILE);
    int64_t nop_id = es_tcm_node_id(store, lp.project, "Field", "NumberOfPulses", ES_TCM_PAR_FILE);
    cbm_node_t nop;
    memset(&nop, 0, sizeof(nop));
    if (nop_id && cbm_store_find_node_by_id(store, nop_id, &nop) == CBM_STORE_OK) {
        int ok = nop.properties_json &&
                 strstr(nop.properties_json, "\"return_type\":\"Ns_M.I_ParInt\"") &&
                 !strstr(nop.properties_json, "enum_value") && nop.start_line == 6;
        if (!ok) {
            fprintf(stderr, "  [ES-TCM] Field NumberOfPulses: line=%d props=%s\n", nop.start_line,
                    nop.properties_json ? nop.properties_json : "(null)");
        }
        failed += !ok;
        cbm_node_free_fields(&nop);
    } else {
        fprintf(stderr, "  [ES-TCM] Field NumberOfPulses missing\n");
        failed++;
    }
    char props[64];
    failed += es_tcm_edge_props(store, par_id, nop_id, "DEFINES", props, sizeof(props)) != 1;
    failed += es_tcm_node_id(store, lp.project, "Field", "Arr", ES_TCM_PAR_FILE) == 0;
    /* Union members likewise. */
    int64_t union_id = es_tcm_node_id(store, lp.project, "Type", "U_Raw", ES_TCM_UNION_FILE);
    int64_t word_id = es_tcm_node_id(store, lp.project, "Field", "Word", ES_TCM_UNION_FILE);
    failed += es_tcm_edge_props(store, union_id, word_id, "DEFINES", props, sizeof(props)) != 1;
    failed += es_tcm_node_id(store, lp.project, "Field", "Bytes", ES_TCM_UNION_FILE) == 0;

    if (failed) {
        es_dump_edge_histogram(store, lp.project);
    }
    es_lang_cleanup(&lp, store);
    free(fx);
    ASSERT_EQ(failed, 0);
    PASS();
}

/* Member-level USAGE edges with line/count, type-level USAGE edges with
 * line/count, and the guards: an unknown member yields nothing, a bare member
 * name never binds a DUT member. Same expectations for both resolve venues. */
static int es_tcm_member_usage_fixture(bool parallel, bool dup_enum) {
    ES_LangProj lp;
    ES_TcMemberFixture *fx = calloc(1, sizeof(*fx));
    if (!fx) {
        return 1;
    }
    cbm_store_t *store = es_tcm_index(&lp, fx, parallel, dup_enum);
    if (!store) {
        es_lang_cleanup(&lp, store);
        free(fx);
        return 1;
    }
    const char *p = lp.project;
    int failed = 0;
    int64_t sm = es_tcm_node_id(store, p, "Method", "stateMachine", ES_TCM_FB_FILE);
    int64_t tc = es_tcm_node_id(store, p, "Method", "Test_Close", ES_TCM_FB_FILE);
    int64_t fb_module = es_tcm_node_id(store, p, "Module", ES_TCM_FB_FILE, ES_TCM_FB_FILE);
    int64_t enum_t = es_tcm_node_id(store, p, "Type", "E_ValveState", ES_TCM_ENUM_FILE);
    int64_t par_t = es_tcm_node_id(store, p, "Type", "T_Par", ES_TCM_PAR_FILE);
    int64_t close_f = es_tcm_node_id(store, p, "Field", "CLOSE", ES_TCM_ENUM_FILE);
    int64_t open_f = es_tcm_node_id(store, p, "Field", "OPEN", ES_TCM_ENUM_FILE);
    int64_t off_f = es_tcm_node_id(store, p, "Field", "OFF", ES_TCM_ALARM_FILE);
    int64_t nop_f = es_tcm_node_id(store, p, "Field", "NumberOfPulses", ES_TCM_PAR_FILE);
    int64_t inner_f = es_tcm_node_id(store, p, "Field", "Inner", ES_TCM_PAR_FILE);
    int64_t depth_f = es_tcm_node_id(store, p, "Field", "Depth", ES_TCM_INNER_FILE);
    failed += !sm || !tc || !fb_module || !enum_t || !par_t || !close_f || !open_f || !off_f ||
              !nop_f || !inner_f || !depth_f;
    if (failed) {
        fprintf(stderr,
                "  [ES-TCM] node lookup: sm=%d tc=%d mod=%d enum=%d par=%d close=%d "
                "open=%d off=%d nop=%d inner=%d depth=%d\n",
                sm != 0, tc != 0, fb_module != 0, enum_t != 0, par_t != 0, close_f != 0,
                open_f != 0, off_f != 0, nop_f != 0, inner_f != 0, depth_f != 0);
    }
    /* Enum members: CASE label, assignment, comparison (lines 32, 33, 35). */
    failed += !es_tcm_expect_usage(store, sm, close_f, "stateMachine->CLOSE", 32, 3);
    failed += !es_tcm_expect_usage(store, sm, open_f, "stateMachine->OPEN", 27, 1);
    failed += !es_tcm_expect_usage(store, tc, close_f, "Test_Close->CLOSE (named arg)", 46, 1);
    /* Library-qualified enum member through the .plcproj namespace alias. */
    failed += !es_tcm_expect_usage(store, sm, off_f, "stateMachine->Ns_M.E_Alarm.OFF", 36, 1);
    /* Struct fields via the FB-level VAR (_par), the VAR_INPUT chain (inPar.Inner.Depth)
     * and the method-local VAR (local.Depth). */
    failed += !es_tcm_expect_usage(store, sm, nop_f, "stateMachine->_par.NumberOfPulses", 28, 1);
    failed += !es_tcm_expect_usage(store, sm, inner_f, "stateMachine->inPar.Inner", 29, 1);
    failed += !es_tcm_expect_usage(store, sm, depth_f, "stateMachine->Depth", 29, 2);
    /* Type-level edges now carry occurrence data too; the set itself is guarded
     * elsewhere. With a same-named enum in the other library the bare type name
     * is ambiguous for the generic resolver, so only the unambiguous case is
     * pinned here. */
    if (!dup_enum) {
        failed += !es_tcm_expect_usage(store, sm, enum_t, "stateMachine->E_ValveState", 27, 5);
        failed += !es_tcm_expect_usage(store, tc, enum_t, "Test_Close->E_ValveState", 46, 1);
        failed += !es_tcm_expect_usage(store, fb_module, par_t, "FB_Drain module->T_Par", 6, 2);
        failed +=
            !es_tcm_expect_usage(store, fb_module, enum_t, "FB_Drain module->E_ValveState", 9, 1);
    } else {
        /* LibM's same-named enum: its CLOSE is never a target of LibApp's references. */
        int64_t dup_close =
            es_tcm_node_id(store, p, "Field", "CLOSE", "LibM/DUTs/E_ValveState.TcDUT");
        int dup_in = es_tcm_inbound(store, dup_close, "USAGE");
        if (dup_close == 0 || dup_in != 0) {
            fprintf(stderr, "  [ES-TCM] LibM E_ValveState.CLOSE: node=%d inbound USAGE=%d\n",
                    dup_close != 0, dup_in);
            failed++;
        }
    }
    /* Guards: `y := CLOSE` (bare) and `E_ValveState.UNKNOWN_MEMBER` add nothing —
     * CLOSE has exactly its two qualified sources; Depth is never bound by the
     * bare-name READS/WRITES fallback (`local.Depth := 2`). */
    int close_in = es_tcm_inbound(store, close_f, "USAGE");
    int depth_writes = es_tcm_inbound(store, depth_f, "WRITES");
    int depth_reads = es_tcm_inbound(store, depth_f, "READS");
    int depth_usage = es_tcm_inbound(store, depth_f, "USAGE");
    if (close_in != 2 || depth_writes != 0 || depth_reads != 0 || depth_usage != 1) {
        fprintf(stderr,
                "  [ES-TCM] guards: CLOSE usage in=%d (want 2), Depth writes=%d reads=%d "
                "usage=%d (want 0/0/1)\n",
                close_in, depth_writes, depth_reads, depth_usage);
        failed++;
    }
    if (failed) {
        es_dump_edge_histogram(store, p);
    }
    es_lang_cleanup(&lp, store);
    free(fx);
    return failed;
}

TEST(es_twincat_member_usage_edges_sequential) {
    ASSERT_EQ(es_tcm_member_usage_fixture(false, false), 0);
    PASS();
}

TEST(es_twincat_member_usage_edges_parallel) {
    ASSERT_EQ(es_tcm_member_usage_fixture(true, false), 0);
    PASS();
}

/* Same expectations when the enum name exists in two libraries: the member
 * binds inside the referencing library, and the now-ambiguous bare name
 * (registry-wise) must not suppress the exact member edge. */
TEST(es_twincat_member_usage_same_name_in_two_libraries_sequential) {
    ASSERT_EQ(es_tcm_member_usage_fixture(false, true), 0);
    PASS();
}

TEST(es_twincat_member_usage_same_name_in_two_libraries_parallel) {
    ASSERT_EQ(es_tcm_member_usage_fixture(true, true), 0);
    PASS();
}

/* Typed-receiver calls: every method below makes exactly one call, so a
 * one-edge expectation pins both the target and the absence of a guess. */
static const char ES_TCC_TIMER[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_Timer\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Timer\nVAR\nEND_VAR\n]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "    <Method Name=\"Start\" Id=\"{2}\">\n"
    "      <Declaration><![CDATA[METHOD Start : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Start := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Property Name=\"Elapsed\" Id=\"{9}\">\n"
    "      <Declaration><![CDATA[PROPERTY Elapsed : TIME\n]]></Declaration>\n"
    "      <Get Name=\"Get\" Id=\"{10}\">\n"
    "        <Declaration><![CDATA[VAR\nEND_VAR\n]]></Declaration>\n"
    "        <Implementation><ST><![CDATA[Elapsed := T#0S;]]></ST></Implementation>\n"
    "      </Get>\n"
    "    </Property>\n"
    "  </POU>\n</TcPlcObject>\n";

/* Same method names as everything the user calls: the generic resolver's decoy. */
static const char ES_TCC_DECOY[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_Decoy\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Decoy\nVAR\nEND_VAR\n]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "    <Method Name=\"Start\" Id=\"{2}\">\n"
    "      <Declaration><![CDATA[METHOD Start : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Start := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"Reset\" Id=\"{3}\">\n"
    "      <Declaration><![CDATA[METHOD Reset : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Reset := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"Fire\" Id=\"{4}\">\n"
    "      <Declaration><![CDATA[METHOD Fire : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Fire := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"Missing\" Id=\"{5}\">\n"
    "      <Declaration><![CDATA[METHOD Missing : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Missing := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"SendRequest\" Id=\"{6}\">\n"
    "      <Declaration><![CDATA[METHOD SendRequest : BOOL\nVAR_INPUT\n\tpath : "
    "STRING;\nEND_VAR\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[SendRequest := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Property Name=\"Elapsed\" Id=\"{9}\">\n"
    "      <Declaration><![CDATA[PROPERTY Elapsed : TIME\n]]></Declaration>\n"
    "      <Get Name=\"Get\" Id=\"{10}\">\n"
    "        <Declaration><![CDATA[VAR\nEND_VAR\n]]></Declaration>\n"
    "        <Implementation><ST><![CDATA[Elapsed := T#0S;]]></ST></Implementation>\n"
    "      </Get>\n"
    "    </Property>\n"
    "  </POU>\n</TcPlcObject>\n";

/* Decoy for the HTTP-service-pattern-named receiver check below (finding 1):
 * its own SendRequest must lose to the ST receiver-typed one on FB_Http. */
static const char ES_TCC_HTTP[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_Http\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Http\nVAR\nEND_VAR\n]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "    <Method Name=\"SendRequest\" Id=\"{2}\">\n"
    "      <Declaration><![CDATA[METHOD SendRequest : BOOL\nVAR_INPUT\n\tpath : "
    "STRING;\nEND_VAR\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[SendRequest := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "  </POU>\n</TcPlcObject>\n";

static const char ES_TCC_BASE[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_Base\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_Base\nVAR\nEND_VAR\n]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "    <Method Name=\"Reset\" Id=\"{2}\">\n"
    "      <Declaration><![CDATA[METHOD Reset : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[Reset := TRUE;]]></ST></Implementation>\n"
    "    </Method>\n"
    "  </POU>\n</TcPlcObject>\n";

/* Cyclic EXTENDS (finding 3a): neither has method Nope. method_of_type's
 * seen-queue must terminate the breadth-first walk instead of looping. */
static const char ES_TCC_CYC_A[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_CycA\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_CycA EXTENDS FB_CycB\nVAR\nEND_VAR\n"
    "]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "  </POU>\n</TcPlcObject>\n";

static const char ES_TCC_CYC_B[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_CycB\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_CycB EXTENDS FB_CycA\nVAR\nEND_VAR\n"
    "]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "  </POU>\n</TcPlcObject>\n";

static const char ES_TCC_USER[] =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<TcPlcObject Version=\"1.1.0.1\">\n"
    "  <POU Name=\"FB_User\" Id=\"{1}\" SpecialFunc=\"None\">\n"
    "    <Declaration><![CDATA[FUNCTION_BLOCK FB_User\nVAR\n"
    "\t_timer : Ns_A.FB_Timer;\n\t_derived : FB_Derived;\n\t_runner : I_Runner;\n"
    "\tHttpClient : FB_Http;\n\t_cyc : FB_CycA;\n\t_ext : Ns_Unknown.FB_Nowhere;\n"
    "END_VAR\n]]></Declaration>\n"
    "    <Implementation><ST><![CDATA[]]></ST></Implementation>\n"
    "    <Method Name=\"CallTimer\" Id=\"{2}\">\n"
    "      <Declaration><![CDATA[METHOD CallTimer : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_timer.Start();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallInherited\" Id=\"{3}\">\n"
    "      <Declaration><![CDATA[METHOD CallInherited : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_derived.Reset();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallItf\" Id=\"{4}\">\n"
    "      <Declaration><![CDATA[METHOD CallItf : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_runner.Fire();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallMissing\" Id=\"{5}\">\n"
    "      <Declaration><![CDATA[METHOD CallMissing : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_timer.Missing();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallService\" Id=\"{6}\">\n"
    "      <Declaration><![CDATA[METHOD CallService : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[HttpClient.SendRequest('/api');]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallCycle\" Id=\"{7}\">\n"
    "      <Declaration><![CDATA[METHOD CallCycle : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_cyc.Nope();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"CallUntyped\" Id=\"{8}\">\n"
    "      <Declaration><![CDATA[METHOD CallUntyped : BOOL\n]]></Declaration>\n"
    "      <Implementation><ST><![CDATA[_ext.Start();]]></ST></Implementation>\n"
    "    </Method>\n"
    "    <Method Name=\"ReadProp\" Id=\"{9}\">\n"
    "      <Declaration><![CDATA[METHOD ReadProp : BOOL\nVAR\n\tt : TIME;\nEND_VAR\n]]>"
    "</Declaration>\n"
    "      <Implementation><ST><![CDATA[t := _timer.Elapsed;]]></ST></Implementation>\n"
    "    </Method>\n"
    "  </POU>\n</TcPlcObject>\n";

static int es_tcc_typed_call_fixture(bool parallel) {
    static char names[ES_TC_PAD_FILES + 12][ES_TC_PATH];
    static char bodies[ES_TC_PAD_FILES + 12][1024];
    ES_LangFile files[ES_TC_PAD_FILES + 12];
    int n = 0;
    files[n++] = (ES_LangFile){"LibA/LibA.plcproj", ES_TC_LIBA_PROJ};
    files[n++] = (ES_LangFile){"LibB/LibB.plcproj", ES_TC_LIBB_PROJ};
    files[n++] = (ES_LangFile){"LibA/POUs/FB_Timer.TcPOU", ES_TCC_TIMER};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_Decoy.TcPOU", ES_TCC_DECOY};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_Http.TcPOU", ES_TCC_HTTP};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_Base.TcPOU", ES_TCC_BASE};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_CycA.TcPOU", ES_TCC_CYC_A};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_CycB.TcPOU", ES_TCC_CYC_B};
    files[n++] = (ES_LangFile){"LibB/POUs/FB_User.TcPOU", ES_TCC_USER};
    snprintf(bodies[n], sizeof(bodies[n]), ES_TC_POU, "FB_Derived",
             "FUNCTION_BLOCK FB_Derived EXTENDS FB_Base");
    files[n] = (ES_LangFile){"LibB/POUs/FB_Derived.TcPOU", bodies[n]};
    n++;
    snprintf(bodies[n], sizeof(bodies[n]), ES_TC_ITF, "I_Runner", "INTERFACE I_Runner");
    files[n] = (ES_LangFile){"LibB/POUs/I_Runner.TcIO", bodies[n]};
    n++;
    for (int i = 0; parallel && i < ES_TC_PAD_FILES; i++) {
        char pad[32];
        char header[64];
        snprintf(pad, sizeof(pad), "FB_Pad%02d", i);
        snprintf(header, sizeof(header), "FUNCTION_BLOCK %s", pad);
        snprintf(names[n], sizeof(names[n]), "LibB/Pad/%s.TcPOU", pad);
        snprintf(bodies[n], sizeof(bodies[n]), ES_TC_POU, pad, header);
        files[n] = (ES_LangFile){names[n], bodies[n]};
        n++;
    }
    const char *old_workers = getenv("CBM_WORKERS");
    char *saved_workers = old_workers ? strdup(old_workers) : NULL;
    if (parallel) {
        cbm_setenv("CBM_WORKERS", "4", 1);
    }
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, files, n);
    if (parallel) {
        if (saved_workers) {
            cbm_setenv("CBM_WORKERS", saved_workers, 1);
        } else {
            cbm_unsetenv("CBM_WORKERS");
        }
    }
    free(saved_workers);
    if (!store) {
        es_lang_cleanup(&lp, store);
        return 1;
    }
    const char *p = lp.project;
    const char *user = "LibB/POUs/FB_User.TcPOU";
    int failed = 0;
    /* Qualified declared type through the .plcproj alias, decoy ignored. */
    failed += !es_tc_expect(store, p, "CallTimer", user, "CALLS", "LibA/POUs/FB_Timer.TcPOU");
    failed += !es_tc_expect_strategy(store, p, "CallTimer", user, "CALLS", "st_receiver_type");
    /* Method found on the EXTENDS base. FB_Decoy also has a Reset, so the
     * strategy check is what proves the base walk fired rather than a
     * same-name guess landing on FB_Base by coincidence. */
    failed += !es_tc_expect(store, p, "CallInherited", user, "CALLS", "LibB/POUs/FB_Base.TcPOU");
    failed += !es_tc_expect_strategy(store, p, "CallInherited", user, "CALLS", "st_receiver_type");
    /* Interface-typed receiver binds the interface's method. */
    failed += !es_tc_expect(store, p, "CallItf", user, "CALLS", "LibB/POUs/I_Runner.TcIO");
    failed += !es_tc_expect_strategy(store, p, "CallItf", user, "CALLS", "st_receiver_type");
    /* Type known, method absent: no edge, not the decoy's Missing. */
    failed += !es_tc_expect(store, p, "CallMissing", user, "CALLS", NULL);
    /* Finding 1: a receiver variable named like an HTTP client library
     * (HttpClient) must not steer the #523 callee-name service bypass away
     * from the exact ST receiver-type target in the parallel venue. */
    failed += !es_tc_expect(store, p, "CallService", user, "CALLS", "LibB/POUs/FB_Http.TcPOU");
    failed += !es_tc_expect_strategy(store, p, "CallService", user, "CALLS", "st_receiver_type");
    /* Finding 3a: cyclic EXTENDS terminates instead of looping, no edge. */
    failed += !es_tc_expect(store, p, "CallCycle", user, "CALLS", NULL);
    /* Finding 3b: an unresolvable declared type falls through to the generic
     * resolver instead of dropping the call outright. */
    failed += !es_tc_expect_none_with_strategy(store, p, "CallUntyped", user, "CALLS",
                                               "st_receiver_type");
    /* Property read: the exact member edge only, no bare-name guess at the decoy. */
    char targets[8][ES_TC_PATH];
    int nt = es_tc_edge_targets(store, p, "ReadProp", user, "USAGE", targets, 8);
    int to_timer = 0;
    int to_decoy = 0;
    for (int i = 0; i < nt && i < 8; i++) {
        to_timer += strcmp(targets[i], "LibA/POUs/FB_Timer.TcPOU") == 0;
        to_decoy += strcmp(targets[i], "LibB/POUs/FB_Decoy.TcPOU") == 0;
    }
    if (to_timer != 1 || to_decoy != 0) {
        fprintf(stderr, "  [ES-TCC] ReadProp USAGE: timer=%d decoy=%d (want 1/0)\n", to_timer,
                to_decoy);
        failed++;
    }
    if (failed) {
        es_dump_edge_histogram(store, p);
    }
    es_lang_cleanup(&lp, store);
    return failed;
}

TEST(es_twincat_typed_receiver_calls_sequential) {
    ASSERT_EQ(es_tcc_typed_call_fixture(false), 0);
    PASS();
}

TEST(es_twincat_typed_receiver_calls_parallel) {
    ASSERT_EQ(es_tcc_typed_call_fixture(true), 0);
    PASS();
}

/* Member resolution never binds a type of another language (a C struct is
 * the only T_Foreign) and prefers a type declared in the referencing file
 * over a same-named one elsewhere in the library. */
TEST(es_twincat_member_usage_never_crosses_languages_or_files) {
    ES_LangProj lp;
    ES_TcMemberFixture *fx = calloc(1, sizeof(*fx));
    ASSERT_NOT_NULL(fx);
    cbm_store_t *store = es_tcm_index(&lp, fx, false, true);
    ASSERT_NOT_NULL(store);
    const char *p = lp.project;
    int failed = 0;
    int64_t c_depth = es_tcm_node_id(store, p, "Field", "Depth", "LibApp/native/foreign.c");
    int c_in = es_tcm_inbound(store, c_depth, "USAGE");
    if (c_depth == 0 || c_in != 0) {
        fprintf(stderr, "  [ES-TCM] C struct field Depth: node=%d inbound USAGE=%d (want 0)\n",
                c_depth != 0, c_in);
        failed++;
    }
    int64_t a_depth = es_tcm_node_id(store, p, "Field", "Depth", "LibApp/Plain/a.st");
    int64_t b_depth = es_tcm_node_id(store, p, "Field", "Depth", "LibApp/Plain/b.st");
    int a_in = es_tcm_inbound(store, a_depth, "USAGE");
    int b_in = es_tcm_inbound(store, b_depth, "USAGE");
    if (a_depth == 0 || b_depth == 0 || a_in != 1 || b_in != 0) {
        fprintf(stderr, "  [ES-TCM] plain-ST T_Loc.Depth: a=%d(in %d) b=%d(in %d), want 1/0\n",
                a_depth != 0, a_in, b_depth != 0, b_in);
        failed++;
    }
    if (failed) {
        es_dump_edge_histogram(store, p);
    }
    es_lang_cleanup(&lp, store);
    free(fx);
    ASSERT_EQ(failed, 0);
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 3: IMPLEMENTS cross-file (Rust trait + struct)
 *
 * Trait defined in a.rs, impl block in b.rs.
 * resolve_impl_traits() looks up both trait_name and struct_name in the
 * project-wide registry.  Expected GREEN when both files are indexed.
 * ══════════════════════════════════════════════════════════════════ */

/* Rust cross-file IMPLEMENTS: trait in trait.rs, impl in impl.rs. */
TEST(es_implements_crossfile_rust) {
    static const ES_LangFile f[] = {
        {"trait.rs",
         "pub trait Greet {\n    fn hello(&self) -> String;\n}\n"},
        {"impl.rs",
         "use crate::trait::Greet;\n\npub struct English;\n\n"
         "impl Greet for English {\n"
         "    fn hello(&self) -> String {\n        String::from(\"hi\")\n    }\n}\n"}};
    /* GREEN: resolve_impl_traits() uses project-wide registry; both Greet
     * (trait.rs) and English (impl.rs) should resolve after definitions pass. */
    ASSERT_TRUE(es_edge_present(f, 2, "IMPLEMENTS", 1)); /* English implements Greet */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 4: IMPLEMENTS same-file (interface / implicit satisfaction)
 *
 * Java `implements`, C# `:` interface, Go implicit method-set satisfaction.
 * ══════════════════════════════════════════════════════════════════ */

/* Java same-file class implements interface — edge depends on whether
 * pass_semantic / pass_parallel distinguishes interface target from class
 * target in base_classes.  Uncertain — annotated but tested. */
TEST(es_implements_samefile_java) {
    static const ES_LangFile f[] = {
        {"Service.java",
         "package app;\n\ninterface Runnable {\n    void run();\n}\n\n"
         "class Service implements Runnable {\n    public void run() {}\n}\n"}};
    /* Uncertain: Java extraction stores both `extends` and `implements` targets
     * in base_classes[].  The semantic pass may emit INHERITS (not IMPLEMENTS)
     * for all of them, or it may check the target node's label.  If the
     * Interface node is created and the pass distinguishes it → IMPLEMENTS edge.
     * If not → this reproduces a gap.  Assert the CORRECT outcome. */
    ASSERT_TRUE(es_edge_present(f, 1, "IMPLEMENTS", 1)); /* Service implements Runnable */
    PASS();
}

/* C# same-file class implements interface. */
TEST(es_implements_samefile_csharp) {
    static const ES_LangFile f[] = {
        {"Worker.cs",
         "namespace App {\n    interface IWorker {\n        void Work();\n    }\n\n"
         "    class Worker : IWorker {\n        public void Work() {}\n    }\n}\n"}};
    /* Uncertain: C# `:` syntax used for both inheritance and interface impl.
     * The semantic pass must check whether the resolved node is an Interface.
     * Assert the correct outcome; RED if pass doesn't distinguish. */
    ASSERT_TRUE(es_edge_present(f, 1, "IMPLEMENTS", 1)); /* Worker implements IWorker */
    PASS();
}

/* Go implicit interface satisfaction — pass_semantic.c
 * cbm_pipeline_implements_go() checks method-set coverage. */
TEST(es_implements_go_implicit) {
    static const ES_LangFile f[] = {
        {"iface.go",
         "package app\n\ntype Stringer interface {\n    String() string\n}\n"},
        {"impl.go",
         "package app\n\ntype MyType struct{ val string }\n\n"
         "func (m MyType) String() string {\n    return m.val\n}\n"}};
    /* GREEN: cbm_pipeline_implements_go() finds MyType satisfies Stringer
     * (both methods present in the same index), emits IMPLEMENTS. */
    ASSERT_TRUE(es_edge_present(f, 2, "IMPLEMENTS", 1)); /* MyType implements Stringer */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 5: OVERRIDE (Go interface method)
 *
 * When Go's method-set satisfaction creates IMPLEMENTS, it also creates
 * an OVERRIDE edge from each implementing method to the interface method.
 * ══════════════════════════════════════════════════════════════════ */

TEST(es_override_go_implicit) {
    static const ES_LangFile f[] = {
        {"iface.go",
         "package app\n\ntype Namer interface {\n    Name() string\n}\n"},
        {"impl.go",
         "package app\n\ntype Entity struct{ name string }\n\n"
         "func (e Entity) Name() string {\n    return e.name\n}\n"}};
    /* GREEN: cbm_pipeline_implements_go() emits OVERRIDE for Entity.Name -> Namer.Name. */
    ASSERT_TRUE(es_edge_present(f, 2, "OVERRIDE", 1));
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 6: DECORATES same-file and cross-file
 *
 * Python decorators (same-file covered by existing P6; cross-file is new).
 * TypeScript class decorators.
 * Java/Kotlin/C# annotations (uncertain — tested to discover gaps).
 * ══════════════════════════════════════════════════════════════════ */

/* Python DECORATES cross-file: decorator defined in decorators.py,
 * applied in service.py via relative import. */
TEST(es_decorates_crossfile_python) {
    static const ES_LangFile f[] = {
        {"decorators.py",
         "def log_call(func):\n    def wrapper(*args, **kwargs):\n"
         "        return func(*args, **kwargs)\n    return wrapper\n"},
        {"service.py",
         "from .decorators import log_call\n\n\n"
         "@log_call\ndef process(x):\n    return x * 2\n"}};
    /* GREEN: relative import resolves (Python OK per P3), decorator name
     * resolves in registry → DECORATES edge process -> log_call. */
    ASSERT_TRUE(es_edge_present(f, 2, "DECORATES", 1));
    PASS();
}

/* TypeScript class decorator — same-file. */
TEST(es_decorates_samefile_typescript) {
    static const ES_LangFile f[] = {
        {"service.ts",
         "function Injectable(target: any): any { return target; }\n\n"
         "@Injectable\nexport class UserService {\n    getUser(id: string) { return id; }\n}\n"}};
    /* Uncertain: TS extraction may or may not populate decorators[] for class
     * decorators.  Assert the correct outcome; RED if TS class decorator
     * extraction is unimplemented. */
    ASSERT_TRUE(es_edge_present(f, 1, "DECORATES", 1));
    PASS();
}

/* Java annotation — same-file.
 * Annotations are syntactically similar to decorators; uncertain if the
 * pipeline emits a DECORATES edge for Java @Annotation. */
TEST(es_decorates_annotation_java) {
    static const ES_LangFile f[] = {
        {"Service.java",
         "package app;\n\nimport java.lang.annotation.*;\n\n"
         "@Retention(RetentionPolicy.RUNTIME)\n@interface Override {}\n\n"
         "class Service {\n    @Override\n    public String toString() { return \"service\"; }\n}\n"}};
    /* Uncertain/RED: Java extraction likely does not populate decorators[] for
     * @Annotation syntax (no Java branch in the decorator extractor confirmed).
     * This test probes whether any DECORATES edge is created.
     * Expected to be RED (count=0) — reproduces the gap if so. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 1);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "DECORATES") : -1;
    fprintf(stderr, "  [ES-EDGE] Java annotation DECORATES got=%d (expected 0 if unimplemented; "
                    "promote to GREEN if edge appears)\n", got);
    es_lang_cleanup(&lp, store);
    /* Assert the CORRECT outcome: annotated method should produce DECORATES. */
    ASSERT_TRUE(got >= 1); /* RED until Java annotation extraction implemented */
    PASS();
}

/* Kotlin annotation — same-file. */
TEST(es_decorates_annotation_kotlin) {
    static const ES_LangFile f[] = {
        {"Service.kt",
         "annotation class Log\n\n"
         "@Log\nfun process(x: Int): Int = x * 2\n"}};
    /* Uncertain/RED: Kotlin decorator/annotation extraction unclear.
     * FAILS (RED) until Kotlin annotation DECORATES is implemented. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 1);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "DECORATES") : -1;
    fprintf(stderr, "  [ES-EDGE] Kotlin annotation DECORATES got=%d\n", got);
    es_lang_cleanup(&lp, store);
    ASSERT_TRUE(got >= 1); /* RED until implemented */
    PASS();
}

/* C# attribute — same-file. */
TEST(es_decorates_attribute_csharp) {
    static const ES_LangFile f[] = {
        {"Service.cs",
         "using System;\n\n[AttributeUsage(AttributeTargets.Method)]\nclass LogAttribute : Attribute {}\n\n"
         "namespace App {\n    class Service {\n        [Log]\n"
         "        public int Process(int x) { return x * 2; }\n    }\n}\n"}};
    /* Uncertain/RED: C# attribute extraction unclear.
     * FAILS (RED) until C# attribute DECORATES is implemented. */
    ES_LangProj lp;
    cbm_store_t *store = es_lang_index_files(&lp, f, 1);
    int got = store ? cbm_store_count_edges_by_type(store, lp.project, "DECORATES") : -1;
    fprintf(stderr, "  [ES-EDGE] C# attribute DECORATES got=%d\n", got);
    es_lang_cleanup(&lp, store);
    ASSERT_TRUE(got >= 1); /* RED until implemented */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 7: USAGE cross-file (type/symbol reference)
 *
 * USAGE edges are created when a type or identifier reference (not a call)
 * resolves in the registry.  pass_usages.c handles this.
 * ══════════════════════════════════════════════════════════════════ */

/* Python constructor syntax is a CALLS edge to the materialized Class node. */
TEST(es_usage_crossfile_python) {
    static const ES_LangFile f[] = {
        {"models.py",
         "class User:\n    def __init__(self, name):\n        self.name = name\n"},
        {"main.py",
         "from .models import User\n\n\ndef create_user(name):\n    return User(name)\n"}};
    ASSERT_EQ(es_exact_edge_by_name(f, 2, "CALLS", "create_user", "User"), 1);
    PASS();
}

/* TypeScript cross-file USAGE: main.ts uses a type from types.ts. */
TEST(es_usage_crossfile_typescript) {
    static const ES_LangFile f[] = {
        {"types.ts",
         "export interface Config {\n    timeout: number;\n}\n"},
        {"main.ts",
         "import { Config } from './types';\n\n"
         "export function create(cfg: Config): string {\n    return String(cfg.timeout);\n}\n"}};
    /* Uncertain: TS USAGE edges for type-only references (interface used as
     * a parameter type annotation).  Assert the correct outcome. */
    ASSERT_TRUE(es_edge_present(f, 2, "USAGE", 1));
    PASS();
}

/* Go cross-file USAGE: main.go references a struct type from types.go. */
TEST(es_usage_crossfile_go) {
    static const ES_LangFile f[] = {
        {"types.go",
         "package app\n\ntype Config struct {\n    Timeout int\n}\n"},
        {"main.go",
         "package app\n\nfunc Create(cfg Config) int {\n    return cfg.Timeout\n}\n"}};
    /* Uncertain: Go USAGE edges for struct type references in function
     * signatures.  Assert the correct outcome. */
    ASSERT_TRUE(es_edge_present(f, 2, "USAGE", 1));
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 8: DATA_FLOWS cross-file
 *
 * DATA_FLOWS is created when an HTTP caller (HTTP_CALLS) and a route
 * handler (HANDLES) are linked through the same Route node.  Cross-file
 * variant: handler in app.py, HTTP caller in client.py.
 * ══════════════════════════════════════════════════════════════════ */

TEST(es_data_flows_crossfile_python) {
    static const ES_LangFile f[] = {
        {"app.py",
         "from flask import Flask\n\napp = Flask(__name__)\n\n\n"
         "@app.route(\"/items\")\ndef list_items():\n    return {\"items\": []}\n"},
        {"client.py",
         "def requests_get(url, params=None):\n    return {\"url\": url}\n\n\n"
         "def fetch_items():\n    return requests_get(\"/items\")\n"}};
    /* GREEN: HANDLES created from app.py route decorator; HTTP_CALLS from
     * client.py requests_get("/items"); DATA_FLOWS links them via the same
     * route path.  Cross-file should work as well as same-file (P6 confirms
     * same-file is GREEN). */
    ASSERT_TRUE(es_edge_present(f, 2, "DATA_FLOWS", 1));
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * FAMILY 9: TESTS cross-file (additional languages beyond Go)
 *
 * pass_tests.c creates TESTS edges from test functions to production
 * functions when a *_test file calls a function in a non-test file.
 * Existing P6 covers Go.  This suite adds Python and TypeScript.
 * ══════════════════════════════════════════════════════════════════ */

/* Python TESTS cross-file: test_service.py tests service.py. */
TEST(es_tests_crossfile_python) {
    static const ES_LangFile f[] = {
        {"service.py",
         "def add(a, b):\n    return a + b\n\n\ndef multiply(a, b):\n    return a * b\n"},
        {"test_service.py",
         "from service import add, multiply\n\n\n"
         "def test_add():\n    result = add(1, 2)\n    assert result == 3\n\n\n"
         "def test_multiply():\n    result = multiply(2, 3)\n    assert result == 6\n"}};
    /* GREEN: Python test_ prefix convention, TESTS_FILE + TESTS expected. */
    ASSERT_TRUE(es_edge_present(f, 2, "TESTS", 1)); /* test_add->add, test_multiply->multiply */
    PASS();
}

/* TypeScript TESTS cross-file: service.test.ts tests service.ts. */
TEST(es_tests_crossfile_typescript) {
    static const ES_LangFile f[] = {
        {"service.ts",
         "export function divide(a: number, b: number): number {\n    return a / b;\n}\n\n"
         "export function subtract(a: number, b: number): number {\n    return a - b;\n}\n"},
        {"service.test.ts",
         "import { divide, subtract } from './service';\n\n"
         "function testDivide() {\n    const r = divide(6, 2);\n}\n\n"
         "function testSubtract() {\n    const r = subtract(5, 3);\n}\n"}};
    /* GREEN: TS .test. prefix convention; TESTS_FILE + TESTS expected. */
    ASSERT_TRUE(es_edge_present(f, 2, "TESTS", 1)); /* testDivide->divide etc. */
    PASS();
}

/* ══════════════════════════════════════════════════════════════════
 * SUITE registration
 * ══════════════════════════════════════════════════════════════════ */

SUITE(edge_structural) {
    /* ── FAMILY 1: CALLS cross-file (all 9 hybrid-LSP languages) ─ */
    /* All expected GREEN: registry is project-wide, cross-file == same-file. */
    RUN_TEST(es_calls_crossfile_go);
    RUN_TEST(es_calls_crossfile_c);
    RUN_TEST(es_calls_crossfile_cpp);
    RUN_TEST(es_calls_crossfile_rust);
    RUN_TEST(es_calls_crossfile_python);
    RUN_TEST(es_calls_crossfile_typescript);
    RUN_TEST(es_calls_crossfile_java);
    RUN_TEST(es_calls_crossfile_kotlin);
    RUN_TEST(es_calls_crossfile_csharp);
    RUN_TEST(es_calls_vue_embedded_issue1410);
    RUN_TEST(es_calls_svelte_embedded_issue1807);

    /* ── FAMILY 2: INHERITS cross-file ────────────────────────── */
    /* GREEN: Java, C#, C++ (extraction confirmed correct). */
    RUN_TEST(es_inherits_crossfile_java);
    RUN_TEST(es_inherits_crossfile_csharp);
    RUN_TEST(es_inherits_crossfile_cpp);
    /* RED: Python, TypeScript, PHP, Kotlin (extraction bugs). */
    RUN_TEST(es_inherits_crossfile_python_red);
    RUN_TEST(es_inherits_crossfile_typescript_red);
    RUN_TEST(es_inherits_crossfile_php_red);
    RUN_TEST(es_inherits_crossfile_kotlin_red);
    /* GREEN: TwinCAT namespace-qualified bases, both resolve venues. */
    RUN_TEST(es_twincat_qualified_base_in_library_sequential);
    RUN_TEST(es_twincat_qualified_base_in_library_parallel);
    RUN_TEST(es_twincat_type_usage_edge_set_unchanged);
    RUN_TEST(es_twincat_dut_members_are_fields_under_type);
    RUN_TEST(es_twincat_member_usage_edges_sequential);
    RUN_TEST(es_twincat_member_usage_edges_parallel);
    RUN_TEST(es_twincat_member_usage_same_name_in_two_libraries_sequential);
    RUN_TEST(es_twincat_member_usage_same_name_in_two_libraries_parallel);
    RUN_TEST(es_twincat_typed_receiver_calls_sequential);
    RUN_TEST(es_twincat_typed_receiver_calls_parallel);
    RUN_TEST(es_twincat_member_usage_never_crosses_languages_or_files);

    /* ── FAMILY 3: IMPLEMENTS cross-file (Rust) ──────────────── */
    /* Expected GREEN: project-wide registry covers both files. */
    RUN_TEST(es_implements_crossfile_rust);

    /* ── FAMILY 4: IMPLEMENTS same-file interface ────────────── */
    /* Uncertain: depends on semantic pass distinguishing Class vs Interface. */
    RUN_TEST(es_implements_samefile_java);
    RUN_TEST(es_implements_samefile_csharp);
    RUN_TEST(es_implements_go_implicit);

    /* ── FAMILY 5: OVERRIDE (Go implicit interface method) ───── */
    /* Expected GREEN: cbm_pipeline_implements_go() emits OVERRIDE. */
    RUN_TEST(es_override_go_implicit);

    /* ── FAMILY 6: DECORATES ─────────────────────────────────── */
    /* GREEN: cross-file Python (relative import + registry resolution). */
    RUN_TEST(es_decorates_crossfile_python);
    /* Uncertain: TypeScript class decorator. */
    RUN_TEST(es_decorates_samefile_typescript);
    /* RED: Java/Kotlin/C# annotation → DECORATES (unimplemented extractors). */
    RUN_TEST(es_decorates_annotation_java);
    RUN_TEST(es_decorates_annotation_kotlin);
    RUN_TEST(es_decorates_attribute_csharp);

    /* ── FAMILY 7: USAGE cross-file ─────────────────────────── */
    /* Uncertain: depends on USAGE extraction for each language. */
    RUN_TEST(es_usage_crossfile_python);
    RUN_TEST(es_usage_crossfile_typescript);
    RUN_TEST(es_usage_crossfile_go);

    /* ── FAMILY 8: DATA_FLOWS cross-file ─────────────────────── */
    /* Expected GREEN: route-intermediated path, language-independent. */
    RUN_TEST(es_data_flows_crossfile_python);

    /* ── FAMILY 9: TESTS cross-file ──────────────────────────── */
    /* Expected GREEN: Python + TypeScript test file conventions. */
    RUN_TEST(es_tests_crossfile_python);
    RUN_TEST(es_tests_crossfile_typescript);
}
