/*
 * engine.c - Git-style version control simulator (pure C99, one file).
 *
 * Build:   gcc engine.c -o engine.exe
 * (strict: gcc -std=c99 -Wall -Wextra -pedantic engine.c -o engine.exe)
 *
 * Protocol: read one command per line from stdin, run it, print exactly ONE
 * line of JSON on stdout, fflush(stdout). Repeat until EOF.
 *
 * Commands: init | add <file> <content> | commit <message> | log |
 *           branch <name> | checkout <name> | merge <name> | undo
 *
 * Data structures (all hand written):
 *   1. Hash table  branch name -> commit id      (g_branches)
 *   2. Hash table  filename    -> content        (commit snapshots, g_work)
 *   3. Linked list of commits (parent pointers + global newest-first list)
 *   4. Graph: a merge commit has two parents
 *   5. Queue: BFS (common ancestor search on merge, reachability for log)
 *   6. Stack: undo (previous branch, previous branch tip, working tree)
 *
 * Behaviour notes:
 *   - "init" creates branch 'main' with no commits yet.
 *   - "add" stages a file in the working tree (replaces content if it exists).
 *   - "commit" snapshots the working tree. Refused if nothing changed.
 *   - "checkout" and "merge" refuse to run with uncommitted changes.
 *   - "merge" always creates a merge commit with 2 parents (no fast-forward),
 *     except when already up to date, or when the current branch is empty.
 *   - "log" lists the commits reachable from HEAD; every other command lists
 *     all commits in the repository.
 *   - "undo" reverts the last add/commit/branch/checkout/merge.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>

/* ======================================================================
 * Memory helpers (never crash: on OOM print a JSON error and exit cleanly)
 * ==================================================================== */

/* Reports out-of-memory as JSON and exits. DS: none. Time: O(1). */
static void die_oom(void)
{
    fputs("{\"ok\":false,\"message\":\"out of memory\"}\n", stdout);
    fflush(stdout);
    exit(1);
}

/* malloc that never returns NULL. DS: none. Time: O(1). */
static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);
    if (!p) die_oom();
    return p;
}

/* realloc that never returns NULL. DS: none. Time: O(n) worst case. */
static void *xrealloc(void *p, size_t n)
{
    void *q = realloc(p, n ? n : 1);
    if (!q) die_oom();
    return q;
}

/* strdup replacement (strdup is not C99). DS: none. Time: O(len). */
static char *xstrdup(const char *s)
{
    size_t n = strlen(s);
    char *p = (char *)xmalloc(n + 1);
    memcpy(p, s, n + 1);
    return p;
}

/* ======================================================================
 * String builder (used to build the JSON line and messages)
 * ==================================================================== */

typedef struct {
    char  *s;
    size_t len, cap;
} SB;

/* Initialise an empty string builder. DS: dynamic array. Time: O(1). */
static void sb_init(SB *b)
{
    b->cap = 256;
    b->len = 0;
    b->s = (char *)xmalloc(b->cap);
    b->s[0] = '\0';
}

/* Append n bytes, growing geometrically. DS: dynamic array. Time: O(n) amortised. */
static void sb_putn(SB *b, const char *t, size_t n)
{
    if (b->len + n + 1 > b->cap) {
        size_t nc = b->cap;
        while (b->len + n + 1 > nc) nc *= 2;
        b->s = (char *)xrealloc(b->s, nc);
        b->cap = nc;
    }
    memcpy(b->s + b->len, t, n);
    b->len += n;
    b->s[b->len] = '\0';
}

/* Append a C string. DS: dynamic array. Time: O(len). */
static void sb_puts(SB *b, const char *t) { sb_putn(b, t, strlen(t)); }

/* Append one char. DS: dynamic array. Time: O(1) amortised. */
static void sb_putc(SB *b, char c) { sb_putn(b, &c, 1); }

/* Empty the builder but keep its memory. DS: dynamic array. Time: O(1). */
static void sb_clear(SB *b) { b->len = 0; b->s[0] = '\0'; }

/* Append t as a quoted, escaped JSON string. DS: dynamic array. Time: O(len). */
static void sb_json(SB *b, const char *t)
{
    const unsigned char *p;
    sb_putc(b, '"');
    for (p = (const unsigned char *)t; *p; p++) {
        switch (*p) {
        case '"':  sb_puts(b, "\\\""); break;
        case '\\': sb_puts(b, "\\\\"); break;
        case '\n': sb_puts(b, "\\n");  break;
        case '\r': sb_puts(b, "\\r");  break;
        case '\t': sb_puts(b, "\\t");  break;
        default:
            if (*p < 0x20) {
                char tmp[8];
                sprintf(tmp, "\\u%04x", (unsigned)*p);
                sb_puts(b, tmp);
            } else {
                sb_putc(b, (char)*p);
            }
        }
    }
    sb_putc(b, '"');
}

/* ======================================================================
 * Data structure 1 & 2: hash table (separate chaining, string -> string)
 * Used for  branch name -> commit id  and  filename -> content.
 * ==================================================================== */

typedef struct Entry {
    char *key, *val;
    struct Entry *next;
} Entry;

typedef struct {
    Entry **b;          /* bucket array */
    size_t nb, count;   /* bucket count, number of entries */
} HT;

/* djb2-style string hash. DS: hash table. Time: O(len). */
static unsigned long hash_str(const char *s)
{
    unsigned long h = 5381UL;
    while (*s) h = ((h << 5) + h) ^ (unsigned char)*s++;
    return h;
}

/* Create an empty hash table with 16 buckets. DS: hash table. Time: O(buckets). */
static HT *ht_new(void)
{
    HT *h = (HT *)xmalloc(sizeof *h);
    size_t i;
    h->nb = 16;
    h->count = 0;
    h->b = (Entry **)xmalloc(h->nb * sizeof(Entry *));
    for (i = 0; i < h->nb; i++) h->b[i] = NULL;
    return h;
}

/* Free a table and everything in it. DS: hash table. Time: O(n + buckets). */
static void ht_free(HT *h)
{
    size_t i;
    if (!h) return;
    for (i = 0; i < h->nb; i++) {
        Entry *e = h->b[i];
        while (e) {
            Entry *n = e->next;
            free(e->key);
            free(e->val);
            free(e);
            e = n;
        }
    }
    free(h->b);
    free(h);
}

/* Find an entry by key. DS: hash table. Time: O(1) average. */
static Entry *ht_find(const HT *h, const char *key)
{
    Entry *e = h->b[hash_str(key) % h->nb];
    while (e) {
        if (strcmp(e->key, key) == 0) return e;
        e = e->next;
    }
    return NULL;
}

/* Get a value or NULL when the key is absent. DS: hash table. Time: O(1) average. */
static const char *ht_get(const HT *h, const char *key)
{
    Entry *e = ht_find(h, key);
    return e ? e->val : NULL;
}

/* Double the bucket count and relink entries. DS: hash table. Time: O(n). */
static void ht_resize(HT *h)
{
    size_t nnb = h->nb * 2, i;
    Entry **nb = (Entry **)xmalloc(nnb * sizeof(Entry *));
    for (i = 0; i < nnb; i++) nb[i] = NULL;
    for (i = 0; i < h->nb; i++) {
        Entry *e = h->b[i];
        while (e) {
            Entry *n = e->next;
            size_t idx = hash_str(e->key) % nnb;
            e->next = nb[idx];
            nb[idx] = e;
            e = n;
        }
    }
    free(h->b);
    h->b = nb;
    h->nb = nnb;
}

/* Insert or replace key -> val (both are copied). DS: hash table.
 * Time: O(1) average (amortised, includes resizing). Returns 1 if new key. */
static int ht_put(HT *h, const char *key, const char *val)
{
    Entry *e = ht_find(h, key);
    size_t idx;
    if (e) {
        char *nv = xstrdup(val);
        free(e->val);
        e->val = nv;
        return 0;
    }
    if (h->count + 1 > h->nb * 2) ht_resize(h);
    e = (Entry *)xmalloc(sizeof *e);
    e->key = xstrdup(key);
    e->val = xstrdup(val);
    idx = hash_str(key) % h->nb;
    e->next = h->b[idx];
    h->b[idx] = e;
    h->count++;
    return 1;
}

/* Delete a key. DS: hash table. Time: O(1) average. Returns 1 if removed. */
static int ht_del(HT *h, const char *key)
{
    size_t idx = hash_str(key) % h->nb;
    Entry *e = h->b[idx], *prev = NULL;
    while (e) {
        if (strcmp(e->key, key) == 0) {
            if (prev) prev->next = e->next; else h->b[idx] = e->next;
            free(e->key);
            free(e->val);
            free(e);
            h->count--;
            return 1;
        }
        prev = e;
        e = e->next;
    }
    return 0;
}

/* Deep copy of a table (used for commit snapshots). DS: hash table. Time: O(n). */
static HT *ht_clone(const HT *src)
{
    HT *d = ht_new();
    size_t i;
    for (i = 0; i < src->nb; i++) {
        Entry *e;
        for (e = src->b[i]; e; e = e->next) ht_put(d, e->key, e->val);
    }
    return d;
}

/* Compare two tables for identical key/value sets. DS: hash table. Time: O(n). */
static int ht_equal(const HT *a, const HT *b)
{
    size_t i;
    if (a->count != b->count) return 0;
    for (i = 0; i < a->nb; i++) {
        Entry *e;
        for (e = a->b[i]; e; e = e->next) {
            const char *v = ht_get(b, e->key);
            if (!v || strcmp(v, e->val) != 0) return 0;
        }
    }
    return 1;
}

/* qsort comparator on entry keys. DS: none. Time: O(len). */
static int cmp_entry(const void *x, const void *y)
{
    return strcmp((*(Entry *const *)x)->key, (*(Entry *const *)y)->key);
}

/* Return entries sorted by key (caller frees the array only), for stable
 * JSON output. DS: hash table. Time: O(n log n). */
static Entry **ht_sorted(const HT *h, size_t *n)
{
    Entry **arr = (Entry **)xmalloc((h->count + 1) * sizeof(Entry *));
    size_t i, k = 0;
    for (i = 0; i < h->nb; i++) {
        Entry *e;
        for (e = h->b[i]; e; e = e->next) arr[k++] = e;
    }
    qsort(arr, k, sizeof(Entry *), cmp_entry);
    *n = k;
    return arr;
}

/* ======================================================================
 * Data structures 3 & 4: commit linked list + graph (up to 2 parents)
 * ==================================================================== */

typedef struct Commit {
    char id[8];                  /* 6 hex chars */
    char *msg;
    char *branch;                /* branch the commit was made on */
    struct Commit *parent[2];    /* parent[0] = first parent, parent[1] = merged-in parent */
    int nparents;                /* 0, 1 or 2 (2 = merge commit: graph edge) */
    HT *snap;                    /* filename -> content */
    int seq;                     /* creation order */
    unsigned a, b;               /* BFS visit stamps */
    struct Commit *next;         /* global list, newest first */
} Commit;

/* ======================================================================
 * Global repository state
 * ==================================================================== */

typedef struct Undo {
    char *cur_before;        /* branch HEAD pointed to before the command */
    char *tip_branch;        /* branch whose tip was changed/created (or NULL) */
    char *tip_before;        /* its previous commit id */
    int   tip_existed;       /* did that branch exist before? */
    HT   *work_before;       /* working tree before the command */
    Commit *made;            /* commit created by the command (or NULL) */
    const char *desc;        /* what the command was, for the message */
    struct Undo *next;       /* stack link */
} Undo;

static int      g_init = 0;
static HT      *g_branches = NULL;   /* branch name -> commit id ("" = no commits) */
static char    *g_cur = NULL;        /* current branch (HEAD) */
static HT      *g_work = NULL;       /* working tree: filename -> content */
static Commit  *g_commits = NULL;    /* all commits, newest first */
static int      g_seq = 0;
static unsigned g_stamp = 0;         /* BFS stamp counter */
static Undo    *g_undo = NULL;       /* undo stack (top) */
static SB       g_ds;                /* "ds" field for the current command */

/* ======================================================================
 * Data structure 5: queue (linked list, FIFO) used by BFS
 * ==================================================================== */

typedef struct QNode {
    Commit *c;
    struct QNode *next;
} QNode;

typedef struct { QNode *head, *tail; } Queue;

/* Init an empty queue. DS: queue. Time: O(1). */
static void q_init(Queue *q) { q->head = q->tail = NULL; }

/* Enqueue at the tail. DS: queue. Time: O(1). */
static void q_push(Queue *q, Commit *c)
{
    QNode *n = (QNode *)xmalloc(sizeof *n);
    n->c = c;
    n->next = NULL;
    if (q->tail) q->tail->next = n; else q->head = n;
    q->tail = n;
}

/* Dequeue from the head (NULL when empty). DS: queue. Time: O(1). */
static Commit *q_pop(Queue *q)
{
    QNode *n = q->head;
    Commit *c;
    if (!n) return NULL;
    c = n->c;
    q->head = n->next;
    if (!q->head) q->tail = NULL;
    free(n);
    return c;
}

/* Free all remaining nodes. DS: queue. Time: O(n). */
static void q_drain(Queue *q) { while (q_pop(q)) { } }

/* ======================================================================
 * Commit helpers
 * ==================================================================== */

/* Look an id up in the global commit list. DS: linked list. Time: O(commits). */
static Commit *find_commit(const char *id)
{
    Commit *c;
    if (!id || !*id) return NULL;
    for (c = g_commits; c; c = c->next)
        if (strcmp(c->id, id) == 0) return c;
    return NULL;
}

/* Feed bytes into a 32-bit FNV-1a hash. DS: none. Time: O(n). */
static uint32_t fnv(uint32_t h, const char *s, size_t n)
{
    size_t i;
    for (i = 0; i < n; i++) {
        h ^= (unsigned char)s[i];
        h *= 16777619u;
    }
    return h;
}

/* Make a unique 6-hex-char id from seq, message and parents. DS: linked list
 * (collision check). Time: O(commits). */
static void make_id(Commit *c)
{
    unsigned salt = 0;
    for (;;) {
        uint32_t h = 2166136261u;
        int i;
        h = fnv(h, (const char *)&c->seq, sizeof c->seq);
        h = fnv(h, (const char *)&salt, sizeof salt);
        h = fnv(h, c->msg, strlen(c->msg));
        for (i = 0; i < c->nparents; i++)
            h = fnv(h, c->parent[i]->id, strlen(c->parent[i]->id));
        sprintf(c->id, "%06lx", (unsigned long)(h & 0xFFFFFFu));
        if (!find_commit(c->id)) return;
        salt++;
    }
}

/* Create a commit and push it on the front of the global list. Takes
 * ownership of snap. DS: linked list + graph. Time: O(commits) (id check). */
static Commit *new_commit(const char *msg, Commit *p0, Commit *p1, HT *snap, const char *branch)
{
    Commit *c = (Commit *)xmalloc(sizeof *c);
    c->msg = xstrdup(msg);
    c->branch = xstrdup(branch);
    c->nparents = 0;
    c->parent[0] = c->parent[1] = NULL;
    if (p0) c->parent[c->nparents++] = p0;
    if (p1) c->parent[c->nparents++] = p1;
    c->snap = snap;
    c->seq = ++g_seq;
    c->a = c->b = 0;
    c->id[0] = '\0';
    make_id(c);
    c->next = g_commits;
    g_commits = c;
    return c;
}

/* Free one commit. DS: hash table (snapshot). Time: O(files). */
static void free_commit(Commit *c)
{
    free(c->msg);
    free(c->branch);
    ht_free(c->snap);
    free(c);
}

/* Free every commit. DS: linked list. Time: O(total size). */
static void free_all_commits(void)
{
    while (g_commits) {
        Commit *n = g_commits->next;
        free_commit(g_commits);
        g_commits = n;
    }
}

/* Tip commit id of a branch ("" if none/unknown). DS: hash table. Time: O(1) avg. */
static const char *tip_id(const char *branch)
{
    const char *v = ht_get(g_branches, branch);
    return v ? v : "";
}

/* Is the working tree identical to the current branch's tip snapshot?
 * DS: hash table. Time: O(files). */
static int is_clean(void)
{
    Commit *t = find_commit(tip_id(g_cur));
    if (!t) return g_work->count == 0;
    return ht_equal(g_work, t->snap);
}

/* BFS over the commit graph from start, marking visited commits with a fresh
 * stamp in field 'a'. Returns the stamp and the number of commits reached.
 * DS: queue + graph. Time: O(V + E). */
static unsigned mark_reachable(Commit *start, int *count)
{
    unsigned st = ++g_stamp;
    Queue q;
    Commit *c;
    int n = 0;
    q_init(&q);
    if (start) { start->a = st; q_push(&q, start); }
    while ((c = q_pop(&q)) != NULL) {
        int i;
        n++;
        for (i = 0; i < c->nparents; i++) {
            Commit *p = c->parent[i];
            if (p->a != st) { p->a = st; q_push(&q, p); }
        }
    }
    q_drain(&q);
    if (count) *count = n;
    return st;
}

/* Find a common ancestor of two commits with BFS. Step 1: BFS from 'ours'
 * marks all its ancestors. Step 2: BFS from 'theirs'; the first commit that
 * carries the mark is the nearest common ancestor. Returns NULL if the
 * histories are unrelated. DS: queue + graph. Time: O(V + E). */
static Commit *common_ancestor(Commit *ours, Commit *theirs)
{
    unsigned s1 = mark_reachable(ours, NULL);
    unsigned s2 = ++g_stamp;
    Queue q;
    Commit *c, *found = NULL;
    q_init(&q);
    theirs->b = s2;
    q_push(&q, theirs);
    while ((c = q_pop(&q)) != NULL) {
        int i;
        if (c->a == s1) { found = c; break; }
        for (i = 0; i < c->nparents; i++) {
            Commit *p = c->parent[i];
            if (p->b != s2) { p->b = s2; q_push(&q, p); }
        }
    }
    q_drain(&q);
    return found;
}

/* ======================================================================
 * Data structure 6: undo stack
 * ==================================================================== */

/* Start an undo record capturing HEAD branch and the working tree.
 * Call BEFORE mutating state. DS: stack. Time: O(files). */
static Undo *undo_begin(const char *desc)
{
    Undo *u = (Undo *)xmalloc(sizeof *u);
    u->cur_before = xstrdup(g_cur);
    u->tip_branch = NULL;
    u->tip_before = NULL;
    u->tip_existed = 0;
    u->work_before = ht_clone(g_work);
    u->made = NULL;
    u->desc = desc;
    u->next = NULL;
    return u;
}

/* Remember the previous tip of a branch that is about to change.
 * DS: stack + hash table. Time: O(1) avg. */
static void undo_track_branch(Undo *u, const char *name)
{
    const char *v = ht_get(g_branches, name);
    u->tip_branch = xstrdup(name);
    if (v) { u->tip_existed = 1; u->tip_before = xstrdup(v); }
}

/* Push the record on the stack. DS: stack. Time: O(1). */
static void undo_push(Undo *u)
{
    u->next = g_undo;
    g_undo = u;
}

/* Free one undo record. DS: stack. Time: O(files). */
static void undo_free(Undo *u)
{
    free(u->cur_before);
    free(u->tip_branch);
    free(u->tip_before);
    ht_free(u->work_before);
    free(u);
}

/* Free the whole stack. DS: stack. Time: O(total size). */
static void undo_clear(void)
{
    while (g_undo) {
        Undo *n = g_undo->next;
        undo_free(g_undo);
        g_undo = n;
    }
}

/* ======================================================================
 * JSON output
 * ==================================================================== */

/* Append a note to the "ds" field: "A | B | C". DS: none. Time: O(len). */
static void ds_note(const char *a, const char *b, const char *c)
{
    if (g_ds.len) sb_puts(&g_ds, " | ");
    sb_puts(&g_ds, a);
    if (b) sb_puts(&g_ds, b);
    if (c) sb_puts(&g_ds, c);
}

/* Build and print the single JSON line, then flush. log_mode=1 restricts
 * "commits" to those reachable from HEAD (BFS with a queue).
 * DS: hash table (sorted dump) + linked list + queue. Time: O(n log n + V + E). */
static void emit(int ok, const char *msg, int log_mode)
{
    SB o;
    size_t n, i;
    Commit *c;
    unsigned st = 0;
    int first;

    sb_init(&o);
    sb_puts(&o, "{\"ok\":");
    sb_puts(&o, ok ? "true" : "false");
    sb_puts(&o, ",\"message\":");
    sb_json(&o, msg);
    sb_puts(&o, ",\"branch\":");
    sb_json(&o, g_init ? g_cur : "");
    sb_puts(&o, ",\"head\":");
    sb_json(&o, g_init ? tip_id(g_cur) : "");

    /* branches */
    sb_puts(&o, ",\"branches\":[");
    if (g_init) {
        Entry **arr = ht_sorted(g_branches, &n);
        for (i = 0; i < n; i++) {
            if (i) sb_putc(&o, ',');
            sb_puts(&o, "{\"name\":");
            sb_json(&o, arr[i]->key);
            sb_puts(&o, ",\"commit\":");
            sb_json(&o, arr[i]->val);
            sb_putc(&o, '}');
        }
        free(arr);
    }
    sb_putc(&o, ']');

    /* commits */
    if (log_mode && g_init) st = mark_reachable(find_commit(tip_id(g_cur)), NULL);
    sb_puts(&o, ",\"commits\":[");
    first = 1;
    for (c = g_commits; c; c = c->next) {
        int k;
        if (log_mode && c->a != st) continue;
        if (!first) sb_putc(&o, ',');
        first = 0;
        sb_puts(&o, "{\"id\":");
        sb_json(&o, c->id);
        sb_puts(&o, ",\"msg\":");
        sb_json(&o, c->msg);
        sb_puts(&o, ",\"parents\":[");
        for (k = 0; k < c->nparents; k++) {
            if (k) sb_putc(&o, ',');
            sb_json(&o, c->parent[k]->id);
        }
        sb_puts(&o, "],\"branch\":");
        sb_json(&o, c->branch);
        sb_putc(&o, '}');
    }
    sb_putc(&o, ']');

    /* files (working tree) */
    sb_puts(&o, ",\"files\":{");
    if (g_init) {
        Entry **arr = ht_sorted(g_work, &n);
        for (i = 0; i < n; i++) {
            if (i) sb_putc(&o, ',');
            sb_json(&o, arr[i]->key);
            sb_putc(&o, ':');
            sb_json(&o, arr[i]->val);
        }
        free(arr);
    }
    sb_putc(&o, '}');

    /* ds */
    sb_puts(&o, ",\"ds\":");
    sb_json(&o, g_ds.len ? g_ds.s : "None: no data structure was modified");
    sb_puts(&o, "}\n");

    fputs(o.s, stdout);
    fflush(stdout);
    free(o.s);
}

/* Build a message from up to 3 pieces and print the reply. DS: none. Time: O(len). */
static void finish(int ok, int log_mode, const char *a, const char *b, const char *c)
{
    SB m;
    sb_init(&m);
    sb_puts(&m, a);
    if (b) sb_puts(&m, b);
    if (c) sb_puts(&m, c);
    emit(ok, m.s, log_mode);
    free(m.s);
}

/* Reject commands used before init. DS: none. Time: O(1). Returns 1 if ready. */
static int need_init(void)
{
    if (g_init) return 1;
    ds_note("None: repository not initialized", NULL, NULL);
    finish(0, 0, "Repository not initialized; run 'init' first", NULL, NULL);
    return 0;
}

/* ======================================================================
 * Commands
 * ==================================================================== */

/* init: (re)create an empty repository with branch 'main'.
 * DS: hash table (branches + working tree). Time: O(1) (O(size) when resetting). */
static void cmd_init(void)
{
    int again = g_init;
    if (g_init) {
        undo_clear();
        free_all_commits();
        ht_free(g_branches);
        ht_free(g_work);
        free(g_cur);
    }
    g_branches = ht_new();
    g_work = ht_new();
    ht_put(g_branches, "main", "");
    g_cur = xstrdup("main");
    g_init = 1;
    ds_note("Hash table: created branch table, inserted branch 'main'", NULL, NULL);
    ds_note("Hash table: created empty working snapshot", NULL, NULL);
    finish(1, 0, again ? "Reinitialized empty repository on branch 'main'"
                       : "Initialized empty repository on branch 'main'", NULL, NULL);
}

/* add <file> <content>: stage a file in the working tree.
 * DS: hash table (filename -> content) + stack (undo). Time: O(files + len). */
static void cmd_add(const char *file, const char *content)
{
    Undo *u;
    int isnew;
    if (!need_init()) return;
    if (!*file) { finish(0, 0, "Usage: add <file> <content>", NULL, NULL); return; }
    if (strlen(file) > 255) { finish(0, 0, "File name too long (max 255 characters)", NULL, NULL); return; }
    u = undo_begin("add");
    isnew = ht_put(g_work, file, content);
    undo_push(u);
    ds_note(isnew ? "Hash table: inserted file '" : "Hash table: updated file '", file, "' in working snapshot");
    ds_note("Stack: pushed undo", NULL, NULL);
    finish(1, 0, "Added '", file, "' to the working tree");
}

/* commit <message>: snapshot the working tree as a new commit.
 * DS: linked list (new commit points to parent) + hash table (snapshot copy,
 * branch tip update) + stack (undo). Time: O(files + commits). */
static void cmd_commit(const char *msg)
{
    Commit *tip, *c;
    Undo *u;
    char num[32];
    if (!need_init()) return;
    if (!*msg) { finish(0, 0, "Usage: commit <message>", NULL, NULL); return; }
    tip = find_commit(tip_id(g_cur));
    if (is_clean()) {
        ds_note("Hash table: compared working snapshot with HEAD snapshot (no change)", NULL, NULL);
        finish(0, 0, "Nothing to commit, working tree clean", NULL, NULL);
        return;
    }
    u = undo_begin("commit");
    undo_track_branch(u, g_cur);
    c = new_commit(msg, tip, NULL, ht_clone(g_work), g_cur);
    ht_put(g_branches, g_cur, c->id);
    u->made = c;
    undo_push(u);
    sprintf(num, "%lu", (unsigned long)c->snap->count);
    ds_note("Linked list: appended commit ", c->id, tip ? " pointing to its parent" : " (root commit)");
    ds_note("Hash table: snapshot of ", num, " file(s) copied; branch tip updated");
    ds_note("Stack: pushed undo", NULL, NULL);
    finish(1, 0, "Committed ", c->id, NULL);
}

/* log: show the history reachable from HEAD.
 * DS: linked list (parent chain) + queue (BFS over the commit graph).
 * Time: O(V + E). */
static void cmd_log(void)
{
    int n = 0;
    char num[32];
    if (!need_init()) return;
    mark_reachable(find_commit(tip_id(g_cur)), &n);
    ds_note("Linked list: walked parent chain from HEAD", NULL, NULL);
    ds_note("Queue: BFS over commit graph (follows merge parents)", NULL, NULL);
    if (n == 0) { finish(1, 1, "No commits yet", NULL, NULL); return; }
    sprintf(num, "%d", n);
    finish(1, 1, num, n == 1 ? " commit reachable from HEAD" : " commits reachable from HEAD", NULL);
}

/* branch <name>: create a branch at the current commit (does not switch).
 * DS: hash table (branch -> commit id) + stack (undo). Time: O(1) average. */
static void cmd_branch(const char *name)
{
    Undo *u;
    const char *p;
    if (!need_init()) return;
    if (!*name) { finish(0, 0, "Usage: branch <name>", NULL, NULL); return; }
    for (p = name; *p; p++)
        if (isspace((unsigned char)*p)) {
            finish(0, 0, "Branch names cannot contain spaces", NULL, NULL);
            return;
        }
    if (strlen(name) > 200) { finish(0, 0, "Branch name too long (max 200 characters)", NULL, NULL); return; }
    if (ht_get(g_branches, name)) {
        ds_note("Hash table: lookup found branch '", name, "' already present");
        finish(0, 0, "Branch '", name, "' already exists");
        return;
    }
    if (!*tip_id(g_cur)) {
        finish(0, 0, "Cannot create a branch before the first commit", NULL, NULL);
        return;
    }
    u = undo_begin("branch creation");
    undo_track_branch(u, name);
    ht_put(g_branches, name, tip_id(g_cur));
    undo_push(u);
    ds_note("Hash table: inserted branch '", name, "'");
    ds_note("Stack: pushed undo", NULL, NULL);
    finish(1, 0, "Created branch '", name, "'");
}

/* checkout <name>: switch HEAD to a branch and load its snapshot.
 * DS: hash table (branch lookup, snapshot copied into working tree) + stack.
 * Time: O(files). */
static void cmd_checkout(const char *name)
{
    Undo *u;
    const char *tv;
    Commit *t;
    if (!need_init()) return;
    if (!*name) { finish(0, 0, "Usage: checkout <name>", NULL, NULL); return; }
    tv = ht_get(g_branches, name);
    if (!tv) {
        ds_note("Hash table: lookup of branch '", name, "' missed");
        finish(0, 0, "Branch '", name, "' does not exist");
        return;
    }
    if (strcmp(name, g_cur) == 0) {
        ds_note("Hash table: looked up branch '", name, "' (already current)");
        finish(1, 0, "Already on '", name, "'");
        return;
    }
    if (!is_clean()) {
        finish(0, 0, "Uncommitted changes in working tree; commit them before checkout", NULL, NULL);
        return;
    }
    u = undo_begin("checkout");
    t = find_commit(tv);
    free(g_cur);
    g_cur = xstrdup(name);
    ht_free(g_work);
    g_work = t ? ht_clone(t->snap) : ht_new();
    undo_push(u);
    ds_note("Hash table: looked up branch '", name, "'");
    ds_note("Hash table: working snapshot replaced from commit's snapshot", NULL, NULL);
    ds_note("Stack: pushed undo", NULL, NULL);
    finish(1, 0, "Switched to branch '", name, "'");
}

/* Null-safe string equality (NULL = file absent). DS: none. Time: O(len). */
static int same(const char *a, const char *b)
{
    if (!a || !b) return a == b;
    return strcmp(a, b) == 0;
}

/* Put every key of src into the key-union table. DS: hash table. Time: O(n). */
static void add_keys(HT *u, const HT *src)
{
    size_t i;
    for (i = 0; i < src->nb; i++) {
        Entry *e;
        for (e = src->b[i]; e; e = e->next) ht_put(u, e->key, "1");
    }
}

/* merge <name>: three-way merge of <name> into the current branch.
 * Uses a BFS (queue) to find the common ancestor, then compares each file in
 * base/ours/theirs (hash tables). One-sided change wins; two different
 * changes = conflict (merge aborted). Otherwise a 2-parent commit is made
 * (graph). DS: queue + graph + hash table + stack. Time: O(V + E + files log files). */
static void cmd_merge(const char *name)
{
    const char *tv;
    Commit *ours, *theirs, *base, *mc;
    HT *empty = NULL, *bs, *keys_ht, *res;
    Entry **keys;
    size_t nk, i;
    SB conf, mm;
    int nconf = 0;
    Undo *u;
    char num[32];

    if (!need_init()) return;
    if (!*name) { finish(0, 0, "Usage: merge <branch>", NULL, NULL); return; }
    tv = ht_get(g_branches, name);
    if (!tv) {
        ds_note("Hash table: lookup of branch '", name, "' missed");
        finish(0, 0, "Branch '", name, "' does not exist");
        return;
    }
    if (strcmp(name, g_cur) == 0) { finish(0, 0, "Cannot merge a branch into itself", NULL, NULL); return; }
    theirs = find_commit(tv);
    if (!theirs) { finish(0, 0, "Branch '", name, "' has no commits to merge"); return; }
    if (!is_clean()) {
        finish(0, 0, "Uncommitted changes in working tree; commit them before merging", NULL, NULL);
        return;
    }
    ours = find_commit(tip_id(g_cur));
    ds_note("Hash table: looked up branch tips", NULL, NULL);

    if (ours == theirs) { finish(1, 0, "Already up to date", NULL, NULL); return; }

    if (!ours) { /* current branch is empty: just adopt the other history */
        u = undo_begin("fast-forward merge");
        undo_track_branch(u, g_cur);
        ht_put(g_branches, g_cur, theirs->id);
        ht_free(g_work);
        g_work = ht_clone(theirs->snap);
        undo_push(u);
        ds_note("Hash table: branch tip moved to ", theirs->id, NULL);
        ds_note("Stack: pushed undo", NULL, NULL);
        finish(1, 0, "Fast-forwarded to ", theirs->id, " (current branch had no commits)");
        return;
    }

    base = common_ancestor(ours, theirs);
    ds_note("Queue: BFS from both tips to find the common ancestor", NULL, NULL);
    if (base == theirs) {
        finish(1, 0, "Already up to date", NULL, NULL);
        return;
    }

    /* three-way comparison */
    bs = base ? base->snap : (empty = ht_new());
    keys_ht = ht_new();
    add_keys(keys_ht, bs);
    add_keys(keys_ht, ours->snap);
    add_keys(keys_ht, theirs->snap);
    keys = ht_sorted(keys_ht, &nk);
    res = ht_new();
    sb_init(&conf);
    for (i = 0; i < nk; i++) {
        const char *k = keys[i]->key;
        const char *b = ht_get(bs, k);
        const char *o = ht_get(ours->snap, k);
        const char *t = ht_get(theirs->snap, k);
        const char *pick = NULL;
        int conflict = 0;
        if (same(o, t))      pick = o;     /* identical on both sides */
        else if (same(o, b)) pick = t;     /* only theirs changed it */
        else if (same(t, b)) pick = o;     /* only ours changed it */
        else conflict = 1;                 /* both changed it differently */
        if (conflict) {
            if (nconf) sb_puts(&conf, ", ");
            sb_puts(&conf, k);
            nconf++;
        } else if (pick) {
            ht_put(res, k, pick);
        }
    }
    free(keys);
    ht_free(keys_ht);
    if (empty) ht_free(empty);

    if (nconf) {
        ds_note("Hash table: three-way file compare found conflict(s); nothing merged", NULL, NULL);
        finish(0, 0, "CONFLICT in ", conf.s, ": both branches changed it differently; merge aborted");
        free(conf.s);
        ht_free(res);
        return;
    }
    free(conf.s);

    sb_init(&mm);
    sb_puts(&mm, "Merge branch '");
    sb_puts(&mm, name);
    sb_puts(&mm, "' into '");
    sb_puts(&mm, g_cur);
    sb_puts(&mm, "'");

    u = undo_begin("merge");
    undo_track_branch(u, g_cur);
    sprintf(num, "%lu", (unsigned long)res->count);
    mc = new_commit(mm.s, ours, theirs, res, g_cur);   /* takes ownership of res */
    ht_put(g_branches, g_cur, mc->id);
    ht_free(g_work);
    g_work = ht_clone(mc->snap);
    u->made = mc;
    undo_push(u);
    free(mm.s);

    ds_note(base ? "Queue: BFS found common ancestor " : "Queue: BFS found no common ancestor (empty base)",
            base ? base->id : NULL, NULL);
    ds_note("Hash table: merged snapshot of ", num, " file(s)");
    ds_note("Graph: merge commit ", mc->id, " has 2 parents");
    ds_note("Stack: pushed undo", NULL, NULL);
    finish(1, 0, "Merged '", name, "' into current branch");
}

/* undo: pop the undo stack and restore HEAD branch, branch tip and working tree.
 * DS: stack (pop) + hash table (branch tip restore) + linked list (remove the
 * undone commit from the front of the history). Time: O(files + commits). */
static void cmd_undo(void)
{
    Undo *u;
    SB m;
    if (!need_init()) return;
    u = g_undo;
    if (!u) {
        ds_note("Stack: empty, nothing to pop", NULL, NULL);
        finish(0, 0, "Nothing to undo", NULL, NULL);
        return;
    }
    g_undo = u->next;

    if (u->made) { /* remove the commit created by the undone command */
        Commit **pp = &g_commits;
        while (*pp && *pp != u->made) pp = &(*pp)->next;
        if (*pp) { *pp = u->made->next; free_commit(u->made); }
        u->made = NULL;
    }
    if (u->tip_branch) {
        if (u->tip_existed) ht_put(g_branches, u->tip_branch, u->tip_before ? u->tip_before : "");
        else ht_del(g_branches, u->tip_branch);
    }
    free(g_cur);
    g_cur = xstrdup(u->cur_before);
    ht_free(g_work);
    g_work = u->work_before;
    u->work_before = NULL;

    sb_init(&m);
    sb_puts(&m, "Undid last ");
    sb_puts(&m, u->desc);
    sb_puts(&m, "; now on branch '");
    sb_puts(&m, g_cur);
    sb_puts(&m, "'");
    ds_note("Stack: popped undo", NULL, NULL);
    ds_note("Hash table: branch tip and working snapshot restored", NULL, NULL);
    emit(1, m.s, 0);
    free(m.s);
    undo_free(u);
}

/* ======================================================================
 * Input handling
 * ==================================================================== */

/* Read one line of any length from stdin (NULL at EOF with no data).
 * NUL bytes become spaces; trailing \r and \n are removed.
 * DS: dynamic array. Time: O(len). */
static char *read_line(void)
{
    size_t cap = 256, len = 0;
    char *buf = (char *)xmalloc(cap);
    int ch;
    while ((ch = fgetc(stdin)) != EOF) {
        if (ch == '\n') break;
        if (ch == '\0') ch = ' ';
        if (len + 2 > cap) { cap *= 2; buf = (char *)xrealloc(buf, cap); }
        buf[len++] = (char)ch;
    }
    if (ch == EOF && len == 0) { free(buf); return NULL; }
    while (len > 0 && buf[len - 1] == '\r') len--;
    buf[len] = '\0';
    return buf;
}

/* Parse a line and run the matching command. DS: none (dispatch).
 * Time: O(len) plus the command's own cost. */
static void run_line(char *line)
{
    char *p = line, *cmd, *rest;
    size_t n, i;

    sb_clear(&g_ds);
    while (*p && isspace((unsigned char)*p)) p++;
    n = strlen(p);
    while (n > 0 && isspace((unsigned char)p[n - 1])) p[--n] = '\0';
    if (!*p) {
        ds_note("Parser: empty line", NULL, NULL);
        finish(0, 0, "Empty command", NULL, NULL);
        return;
    }
    cmd = p;
    while (*p && !isspace((unsigned char)*p)) p++;
    if (*p) *p++ = '\0';
    while (*p && isspace((unsigned char)*p)) p++;
    rest = p;
    for (i = 0; cmd[i]; i++) cmd[i] = (char)tolower((unsigned char)cmd[i]);

    if (strcmp(cmd, "init") == 0)          cmd_init();
    else if (strcmp(cmd, "add") == 0) {
        char *file = rest, *content = rest;
        while (*content && !isspace((unsigned char)*content)) content++;
        if (*content) *content++ = '\0';
        while (*content && isspace((unsigned char)*content)) content++;
        cmd_add(file, content);
    }
    else if (strcmp(cmd, "commit") == 0)   cmd_commit(rest);
    else if (strcmp(cmd, "log") == 0)      cmd_log();
    else if (strcmp(cmd, "branch") == 0)   cmd_branch(rest);
    else if (strcmp(cmd, "checkout") == 0) cmd_checkout(rest);
    else if (strcmp(cmd, "merge") == 0)    cmd_merge(rest);
    else if (strcmp(cmd, "undo") == 0)     cmd_undo();
    else {
        char shown[72];
        strncpy(shown, cmd, 64);
        shown[64] = '\0';
        ds_note("Parser: unknown command", NULL, NULL);
        finish(0, 0, "Unknown command '", shown,
               "'. Use: init, add, commit, log, branch, checkout, merge, undo");
    }
}

/* Main loop: read a line, run it, print one JSON line, repeat until EOF.
 * DS: none. Time: O(total input). */
int main(void)
{
    char *line;
    sb_init(&g_ds);
    while ((line = read_line()) != NULL) {
        run_line(line);
        free(line);
    }
    return 0;
}
