#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <regex>
#define MAX_VARS 16  // the largest allowed number of inputs
#define MAX_SIZE 256 // the number of initially allocated objects
#define KC_GG_NULL (0x7FFFFFFF)
int Num = rand();
/*************************************************************
                     Various helpers
**************************************************************/

// operations on variables and literals
static inline int kc_v2l(int Var, int c)
{
    assert(Var >= 0 && !(c >> 1));
    return Var + Var + c;
}
static inline int kc_l2v(int Lit)
{
    assert(Lit >= 0);
    return Lit >> 1;
}
static inline int kc_l2c(int Lit)
{
    assert(Lit >= 0);
    return Lit & 1;
}
static inline int kc_lnot(int Lit)
{
    assert(Lit >= 0);
    return Lit ^ 1;
}
static inline int kc_lnotc(int Lit, int c)
{
    assert(Lit >= 0);
    return Lit ^ (int)(c > 0);
}
static inline int kc_lreg(int Lit)
{
    assert(Lit >= 0);
    return Lit & ~01;
}

// min/max/abs
static inline int kc_abs(int a) { return a < 0 ? -a : a; }
static inline int kc_max(int a, int b) { return a > b ? a : b; }
static inline int kc_min(int a, int b) { return a < b ? a : b; }

// truth table size in 64-bit words
static inline int kc_truth_word_num(int n) { return n <= 6 ? 1 : 1 << (n - 6); }

// swapping two variables
#define KC_SWAP(Type, a, b) \
    {                       \
        Type t = a;         \
        a = b;              \
        b = t;              \
    }

/*************************************************************
                 Vector of 32-bit integers
**************************************************************/

typedef struct kc_vi_
{
    int size;
    int cap;
    int *ptr;
} kc_vi;

// iterator through the entries in the vector
#define kc_vi_for_each_entry(v, entry, i) \
    for (i = 0; (i < (v)->size) && (((entry) = kc_vi_read((v), i)), 1); i++)

static inline void kc_vi_start(kc_vi *v, int cap)
{
    v->size = 0;
    v->cap = cap;
    v->ptr = (int *)malloc(sizeof(int) * v->cap);
}
static inline void kc_vi_stop(kc_vi *v) { free(v->ptr); }
static inline int *kc_vi_array(kc_vi *v) { return v->ptr; }
static inline int kc_vi_read(kc_vi *v, int k)
{
    assert(k < v->size);
    return v->ptr[k];
}
static inline void kc_vi_write(kc_vi *v, int k, int e)
{
    assert(k < v->size);
    v->ptr[k] = e;
}
static inline int kc_vi_size(kc_vi *v) { return v->size; }
static inline void kc_vi_resize(kc_vi *v, int k)
{
    assert(k <= v->size);
    v->size = k;
} // only safe to shrink !!
static inline int kc_vi_pop(kc_vi *v)
{
    assert(v->size > 0);
    return v->ptr[--v->size];
}
static inline void kc_vi_grow(kc_vi *v)
{
    if (v->size < v->cap)
        return;
    int newcap = (v->cap < 4) ? 8 : (v->cap / 2) * 3;
    v->ptr = (int *)realloc(v->ptr, sizeof(int) * newcap);
    if (v->ptr == NULL)
    {
        printf("Failed to realloc memory from %.1f MB to %.1f MB.\n", 4.0 * v->cap / (1 << 20), 4.0 * newcap / (1 << 20));
        fflush(stdout);
    }
    v->cap = newcap;
}
static inline void kc_vi_push(kc_vi *v, int e)
{
    kc_vi_grow(v);
    v->ptr[v->size++] = e;
}
static inline void kc_vi_fill(kc_vi *v, int n, int fill)
{
    int i;
    for (i = 0; i < n; i++)
        kc_vi_push(v, fill);
}
static inline int kc_vi_remove(kc_vi *v, int e)
{
    int j;
    for (j = 0; j < v->size; j++)
        if (v->ptr[j] == e)
            break;
    if (j == v->size)
        return 0;
    for (; j < v->size - 1; j++)
        v->ptr[j] = v->ptr[j + 1];
    kc_vi_resize(v, v->size - 1);
    return 1;
}
static inline void kc_vi_print(kc_vi *v)
{
    printf("Array with %d entries:", v->size);
    int i, entry;
    kc_vi_for_each_entry(v, entry, i)
        printf(" %d", entry);
    printf("\n");
}

/*************************************************************
                 Vector of truth tables
**************************************************************/

#ifdef _WIN32
typedef unsigned __int64 kc_uint64; // 32-bit windows
#else
typedef long long unsigned kc_uint64; // other platforms
#endif

typedef struct kc_vt_
{
    int size;
    int cap;
    int words;
    kc_uint64 *ptr;
} kc_vt;

static inline kc_uint64 *kc_vt_array(kc_vt *v) { return v->ptr; }
static inline int kc_vt_words(kc_vt *v) { return v->words; }
static inline int kc_vt_size(kc_vt *v) { return v->size; }
static inline void kc_vt_resize(kc_vt *v, int ttNum)
{
    assert(ttNum <= v->size);
    v->size = ttNum;
} // only safe to shrink !!
static inline void kc_vt_shrink(kc_vt *v, int num)
{
    assert(num <= v->size);
    v->size -= num;
}
static inline kc_uint64 *kc_vt_read(kc_vt *v, int ttId)
{
    assert(ttId < v->size);
    return v->ptr + ttId * v->words;
}
static inline void kc_vt_grow(kc_vt *v)
{
    if (v->size == v->cap)
    {
        int newcap = (v->cap < 4) ? 8 : (v->cap / 2) * 3;
        v->ptr = (kc_uint64 *)realloc(v->ptr, 8 * newcap * v->words);
        if (v->ptr == NULL)
        {
            printf("Failed to realloc memory from %.1f MB to %.1f MB.\n", 4.0 * v->cap * v->words / (1 << 20), 4.0 * newcap * v->words / (1 << 20));
            fflush(stdout);
        }
        v->cap = newcap;
    }
}
static inline kc_uint64 *kc_vt_append(kc_vt *v)
{
    kc_vt_grow(v);
    return v->ptr + v->size++ * v->words;
}
static inline void kc_vt_move(kc_vt *v, kc_vt *v2, int ttId)
{
    assert(v->words == v2->words);
    memmove(kc_vt_append(v), kc_vt_read(v2, ttId), 8 * v->words);
}

/*************************************************************
               Initialization of truth tables
**************************************************************/

static kc_uint64 s_Truths6[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000};
static kc_uint64 s_Truths6Neg[6] = {
    0x5555555555555555,
    0x3333333333333333,
    0x0F0F0F0F0F0F0F0F,
    0x00FF00FF00FF00FF,
    0x0000FFFF0000FFFF,
    0x00000000FFFFFFFF};

static inline void kc_vt_start(kc_vt *v, int cap, int words)
{
    v->size = 0;
    v->cap = cap;
    v->words = words;
    v->ptr = (kc_uint64 *)malloc(8 * v->cap * v->words);
}
static inline void kc_vt_start_truth(kc_vt *v, int nvars)
{
    int i, k;
    v->words = kc_truth_word_num(nvars);
    v->size = 2 * (nvars + 1);
    v->cap = 6 * (nvars + 1);
    v->ptr = (kc_uint64 *)malloc(8 * v->words * v->cap);
    memset(v->ptr, 0, 8 * v->words);
    memset(v->ptr + v->words, 0xFF, 8 * v->words);
    for (i = 0; i < 2 * nvars; i++)
    {
        kc_uint64 *tt = v->ptr + (i + 2) * v->words;
        if (i / 2 < 6)
            for (k = 0; k < v->words; k++)
                tt[k] = s_Truths6[i / 2];
        else
            for (k = 0; k < v->words; k++)
                tt[k] = (k & (1 << (i / 2 - 6))) ? ~(kc_uint64)0 : 0;
        if (i & 1)
            for (k = 0; k < v->words; k++)
                tt[k] = ~tt[k];
        // printf( "lit = %2d  ", i+2 ); kc_vt_print(v, i+2);
    }
}
static inline void kc_vt_stop(kc_vt *v) { free(v->ptr); }
static inline void kc_vt_dup(kc_vt *vNew, kc_vt *v)
{
    kc_vt_start(vNew, v->cap, v->words);
    memmove(kc_vt_array(vNew), kc_vt_array(v), 8 * v->size * v->words);
    vNew->size = v->size;
}

/*************************************************************
             Boolean operations on truth tables
**************************************************************/

static inline int kc_vt_and(kc_vt *v, int ttA, int ttB)
{
    kc_uint64 *pF = kc_vt_append(v);
    int i;
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    for (i = 0; i < v->words; i++)
        pF[i] = pA[i] & pB[i];
    return v->size - 1;
}
static inline int kc_vt_xor(kc_vt *v, int ttA, int ttB)
{
    kc_uint64 *pF = kc_vt_append(v);
    int i;
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    for (i = 0; i < v->words; i++)
        pF[i] = pA[i] ^ pB[i];
    return v->size - 1;
}
static inline int kc_vt_inv(kc_vt *v, int ttA)
{
    kc_uint64 *pF = kc_vt_append(v);
    int i;
    kc_uint64 *pA = kc_vt_read(v, ttA);
    for (i = 0; i < v->words; i++)
        pF[i] = ~pA[i];
    return v->size - 1;
}
static inline int kc_vt_is_equal(kc_vt *v, int ttA, int ttB)
{
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    int i;
    for (i = 0; i < v->words; i++)
        if (pA[i] != pB[i])
            return 0;
    return 1;
}
static inline int kc_vt_is_equal2(kc_vt *vA, int ttA, kc_vt *vB, int ttB)
{
    kc_uint64 *pA = kc_vt_read(vA, ttA);
    kc_uint64 *pB = kc_vt_read(vB, ttB);
    int i;
    assert(vA->words == vB->words);
    for (i = 0; i < vA->words; i++)
        if (pA[i] != pB[i])
            return 0;
    return 1;
}

/*************************************************************
                 Printing truth tables
**************************************************************/

// printing in hexadecimal
static inline void kc_vt_print_int(kc_vt *v, int ttA)
{
    kc_uint64 *pA = kc_vt_read(v, ttA);
    int k, Digit, nDigits = v->words * 16;
    for (k = nDigits - 1; k >= 0; k--)
    {
        Digit = (int)((pA[k / 16] >> ((k % 16) * 4)) & 15);
        if (Digit < 10)
            printf("%d", Digit);
        else
            printf("%c", 'A' + Digit - 10);
    }
}
static inline void kc_vt_print(kc_vt *v, int ttA)
{
    kc_vt_print_int(v, ttA);
    printf("\n");
}
static inline void kc_vt_print_all(kc_vt *v)
{
    int i;
    printf("The array contains %d truth tables of size %d words:\n", v->size, v->words);
    for (i = 0; i < v->size; i++)
    {
        printf("%2d : ", i);
        kc_vt_print(v, i);
    }
}

// printing in binary
static inline void kc_vt_print2_int(kc_vt *v, int ttA)
{
    kc_uint64 *pA = kc_vt_read(v, ttA);
    int k;
    for (k = v->words * 64 - 1; k >= 0; k--)
        printf("%c", '0' + (int)((pA[k / 64] >> (k % 64)) & 1));
}
static inline void kc_vt_print2(kc_vt *v, int ttA)
{
    kc_vt_print2_int(v, ttA);
    printf("\n");
}
static inline void kc_vt_print2_all(kc_vt *v)
{
    int i;
    printf("The array contains %d truth tables of size %d words:\n", v->size, v->words);
    for (i = 0; i < v->size; i++)
    {
        printf("%2d : ", i);
        kc_vt_print2(v, i);
    }
}

/*************************************************************
                 Gate graph data structure
**************************************************************/

typedef struct kc_gg_
{
    int nins; // the number of primary inputs
    int size; // the number of objects, including const0, primary inputs, and internal nodes if any
    int cap;  // the number of objects allocated
    // int tid;     // the current traversal ID
    kc_vi tids;  // the last visited tranversal ID of each object
    kc_vi fans;  // the fanins of objects
    kc_vi tops;  // the output literals
    kc_vt funcs; // the truth tables used for temporary cofactoring
    kc_vt tts;   // the truth tables of each literal (pos and neg polarity of each object)
    kc_vt outs;  // the primary output function(s) given by the user
} kc_gg;

// reading fanins
static inline int kc_gg_fanin(kc_gg *p, int v, int n)
{
    assert(n == 0 || n == 1);
    return kc_vi_read(&p->fans, 2 * v + n);
}
static inline int kc_gg_is_xor(kc_gg *p, int v) { return kc_gg_fanin(p, v, 0) > kc_gg_fanin(p, v, 1); }
static inline int kc_gg_is_node(kc_gg *p, int v) { return v >= 1 + p->nins; }
static inline int kc_gg_is_pi(kc_gg *p, int v) { return v >= 1 && v <= p->nins; }
static inline int kc_gg_is_const0(kc_gg *p, int v) { return v == 0; }
static inline int kc_gg_pi_num(kc_gg *p) { return p->nins; }
static inline int kc_gg_po_num(kc_gg *p) { return kc_vt_size(&p->outs); }
static inline int kc_gg_node_num(kc_gg *p) { return p->size - 1 - p->nins; }

// managing traversal IDs
// static inline int kc_gg_tid_increment(kc_gg *p)
// {
//     assert(p->tid < 0x7FFFFFFF);
//     p->tid++;
//     return p->tid;
// }

// static inline int kc_gg_tid_is_cur(kc_gg *p, int v) { return kc_vi_read(&p->tids, v) == p->tid; }
// static inline int kc_gg_tid_set_cur(kc_gg *p, int v)
// {
//     kc_vi_write(&p->tids, v, p->tid);
//     return 1;
// }
// static inline int kc_gg_tid_update(kc_gg *p, int v)
// {
//     if (kc_gg_tid_is_cur(p, v))
//         return 0;
//     return kc_gg_tid_set_cur(p, v);
// }

// constructor and destructor
static inline kc_gg *kc_gg_start(int nins, kc_vt *outs)
{
    kc_gg *gg = (kc_gg *)malloc(sizeof(kc_gg));
    gg->nins = nins;
    gg->size = 1 + nins;
    gg->cap = MAX_SIZE;
    // gg->tid = 1;
    kc_vi_start(&gg->tids, 2 * gg->cap);
    kc_vi_fill(&gg->tids, gg->size, 0);
    kc_vi_start(&gg->fans, 2 * gg->cap);
    kc_vi_fill(&gg->fans, 2 * gg->size, -1);
    kc_vi_start(&gg->tops, outs->size);
    kc_vt_start(&gg->funcs, 3 * gg->size, kc_truth_word_num(nins));
    kc_vt_start_truth(&gg->tts, nins);
    kc_vt_dup(&gg->outs, outs);
    return gg;
}
static inline void kc_gg_stop(kc_gg *gg)
{
    if (gg == NULL)
        return;
    kc_vt_stop(&gg->outs);
    kc_vt_stop(&gg->funcs);
    kc_vt_stop(&gg->tts);
    kc_vi_stop(&gg->tids);
    kc_vi_stop(&gg->fans);
    kc_vi_stop(&gg->tops);
    free(gg);
}

// managing internal nodes
static inline int kc_gg_hash_node(kc_gg *gg, int lit1, int lit2, int ttId)
{
    int i;
    // compare nodes (structural hashing)
    for (i = 1 + gg->nins; i < gg->size; i++)
        if (kc_gg_fanin(gg, i, 0) == lit1 && kc_gg_fanin(gg, i, 1) == lit2)
            return kc_v2l(i, 0);
    // compare functions (functional hashing)
    for (i = 0; i < 2 * gg->size; i++)
        if (kc_vt_is_equal(&gg->tts, ttId, i))
            return i;
    return -1;
}
static inline int kc_gg_append_node(kc_gg *gg, int lit1, int lit2, int ttId)
{
    gg->size++;
    kc_vi_push(&gg->fans, lit1);
    kc_vi_push(&gg->fans, lit2);
    kc_vi_push(&gg->tids, 0);
    kc_vt_inv(&gg->tts, ttId);
    assert(gg->tts.size == 2 * gg->size); // one truth table for each literal
    return kc_v2l(gg->size - 1, 0);
}

// managing internal functions
static inline int kc_gg_hash_function(kc_gg *gg, int ttId)
{
    int i;
    for (i = 0; i < 2 * gg->size; i++)
        if (kc_vt_is_equal2(&gg->tts, i, &gg->funcs, ttId))
            return i;
    return -1;
}

// Boolean operations
static inline int kc_gg_and(kc_gg *gg, int lit1, int lit2)
{
    if (lit1 == 0)
        return 0;
    if (lit2 == 0)
        return 0;
    if (lit1 == 1)
        return lit2;
    if (lit2 == 1)
        return lit1;
    if (lit1 == lit2)
        return lit1;
    if ((lit1 ^ lit2) == 1)
        return 0;
    if (lit1 > lit2)
        KC_SWAP(int, lit1, lit2)
    assert(lit1 < lit2);
    int ttId = kc_vt_and(&gg->tts, lit1, lit2);
    int lit = kc_gg_hash_node(gg, lit1, lit2, ttId);
    if (lit == -1)
        return kc_gg_append_node(gg, lit1, lit2, ttId);
    kc_vt_resize(&gg->tts, ttId);
    return lit;
}
static inline int kc_gg_xor(kc_gg *gg, int lit1, int lit2)
{
    if (lit1 == 1)
        return (lit2 ^ 1);
    if (lit2 == 1)
        return (lit1 ^ 1);
    if (lit1 == 0)
        return lit2;
    if (lit2 == 0)
        return lit1;
    if (lit1 == lit2)
        return 0;
    if ((lit1 ^ lit2) == 1)
        return 1;
    if (lit1 < lit2)
        KC_SWAP(int, lit1, lit2)
    assert(lit1 > lit2);
    int ttId = kc_vt_xor(&gg->tts, lit1, lit2);
    int lit = kc_gg_hash_node(gg, lit1, lit2, ttId);
    if (lit == -1)
        return kc_gg_append_node(gg, lit1, lit2, ttId);
    kc_vt_resize(&gg->tts, ttId);
    return lit;
}
static inline int kc_gg_or(kc_gg *gg, int lit1, int lit2) { return kc_lnot(kc_gg_and(gg, kc_lnot(lit1), kc_lnot(lit2))); }
static inline int kc_gg_mux(kc_gg *gg, int ctrl, int lit1, int lit0) { return kc_gg_or(gg, kc_gg_and(gg, ctrl, lit1), kc_gg_and(gg, kc_lnot(ctrl), lit0)); }
static inline int kc_gg_and_xor(kc_gg *gg, int ctrl, int lit1, int lit0) { return kc_gg_xor(gg, kc_gg_and(gg, ctrl, lit1), lit0); }

// counting nodes
// int kc_gg_node_count_rec(kc_gg *gg, int lit)
// {
//     int res = 1, var = kc_l2v(lit);
//     if (var <= gg->nins || !kc_gg_tid_update(gg, var))
//         return 0;
//     res += kc_gg_node_count_rec(gg, kc_vi_read(&gg->fans, lit));
//     res += kc_gg_node_count_rec(gg, kc_vi_read(&gg->fans, kc_lnot(lit)));
//     return res;
// }
// int kc_gg_node_count1(kc_gg *gg, int lit)
// {
//     kc_gg_tid_increment(gg);
//     return kc_gg_node_count_rec(gg, lit);
// }
// int kc_gg_node_count2(kc_gg *gg, int lit0, int lit1)
// {
//     kc_gg_tid_increment(gg);
//     return kc_gg_node_count_rec(gg, lit0) + kc_gg_node_count_rec(gg, lit1);
// }
// int kc_gg_node_count(kc_gg *gg)
// {
//     int i, top, Count = 0;
//     kc_gg_tid_increment(gg);
//     kc_vi_for_each_entry(&gg->tops, top, i)
//         Count += kc_gg_node_count_rec(gg, top);
//     return Count;
// }

// // counting levels
// int kc_gg_level_rec(kc_gg *gg, int *levs, int lit)
// {
//     int res0, res1, var = kc_l2v(lit);
//     if (var <= gg->nins || !kc_gg_tid_update(gg, var))
//         return levs[var];
//     res0 = kc_gg_level_rec(gg, levs, kc_vi_read(&gg->fans, lit));
//     res1 = kc_gg_level_rec(gg, levs, kc_vi_read(&gg->fans, kc_lnot(lit)));
//     return (levs[var] = 1 + kc_max(res0, res1));
// }
// int kc_gg_level(kc_gg *gg)
// {
//     int i, top, levMax = 0;
//     int *levs = (int *)calloc(sizeof(int), gg->size);
//     kc_gg_tid_increment(gg);
//     kc_vi_for_each_entry(&gg->tops, top, i)
//         levMax = kc_max(levMax, kc_gg_level_rec(gg, levs, top));
//     free(levs);
//     return levMax;
// }

// printing the graph
void kc_gg_print_lit(int lit, int nVars)
{
    assert(lit >= 0);
    if (lit < 2)
        printf("%d", lit);
    else if (lit < 2 * (nVars + 1))
        printf("%s%c", kc_l2c(lit) ? "~" : "", (char)(96 + kc_l2v(lit)));
    else
        printf("%s%02d", kc_l2c(lit) ? "~n" : "n", kc_l2v(lit));
}
void kc_gg_print(kc_gg *gg, int verbose)
{
    int fPrintGraphs = verbose;
    int fPrintTruths = gg->nins <= 8;
    int i, top, nLevels, nCount[2] = {0};
    // if (!fPrintGraphs)
    // {
    //     printf("The graph contains %d nodes and spans %d levels.\n", kc_gg_node_count(gg), kc_gg_level(gg));
    //     return;
    // }
    // mark used nodes with the new travId
    // nLevels = kc_gg_level(gg);
    // print const and inputs
    if (fPrintTruths)
        kc_vt_print_int(&gg->tts, 0), printf(" ");
    printf("n%02d = 0\n", 0);
    for (i = 1; i <= gg->nins; i++)
    {
        if (fPrintTruths)
            kc_vt_print_int(&gg->tts, 2 * i), printf(" ");
        printf("n%02d = %c\n", i, (char)(96 + i));
    }
    // print used nodes
    int count = 1;
    for (i = gg->nins + 1; i < gg->size; i++)
        // if (kc_gg_tid_is_cur(gg, i))
        // {
        printf("%d ", count++);
    if (fPrintTruths)
        kc_vt_print_int(&gg->tts, 2 * i), printf(" ");
    printf("n%02d = ", i);
    kc_gg_print_lit(kc_gg_fanin(gg, i, 0), gg->nins);

    printf(" %c ", kc_gg_is_xor(gg, i) ? '^' : '&');
    kc_gg_print_lit(kc_gg_fanin(gg, i, 1), gg->nins);
    printf("\n");
    nCount[kc_gg_is_xor(gg, i)]++;
    // }
    // print outputs
    kc_vi_for_each_entry(&gg->tops, top, i)
    {
        if (fPrintTruths)
            kc_vt_print_int(&gg->tts, top), printf(" ");
        printf("po%d = ", i);
        kc_gg_print_lit(top, gg->nins);
        printf("\n");
    }
    printf("The graph contains %d nodes (%d ands and %d xors)",
           nCount[0] + nCount[1], nCount[0], nCount[1]);
}

// duplicates AIG while only copying used nodes (also expands xors into ands as needed)
kc_gg *kc_gg_dup(kc_gg *gg, int only_and)
{
    kc_gg *ggNew = kc_gg_start(gg->nins, &gg->outs);
    int i, top, *pCopy = (int *)calloc(sizeof(int), 2 * gg->size);
    for (i = 0; i < 2 * (1 + gg->nins); i++)
        pCopy[i] = i;
    for (i = 1 + gg->nins; i < gg->size; i++)
    {
        // if (kc_gg_tid_is_cur(gg, i))
        // {
        int lit0 = kc_gg_fanin(gg, i, 0);
        int lit1 = kc_gg_fanin(gg, i, 1);
        if (!kc_gg_is_xor(gg, i))
            pCopy[2 * i] = kc_gg_and(ggNew, pCopy[lit0], pCopy[lit1]);
        else if (only_and)
            pCopy[2 * i] = kc_gg_mux(ggNew, pCopy[lit0], kc_lnot(pCopy[lit1]), pCopy[lit1]);
        else
            pCopy[2 * i] = kc_gg_xor(ggNew, pCopy[lit0], pCopy[lit1]);
        pCopy[2 * i + 1] = kc_lnot(pCopy[2 * i]);
        // }
    }
    kc_vi_for_each_entry(&gg->tops, top, i)
        kc_vi_push(&ggNew->tops, pCopy[top]);
    free(pCopy);
    return ggNew;
}

// compares truth tables against the specification
void kc_gg_verify(kc_gg *gg)
{
    int i, top, nFailed = 0;
    kc_vi_for_each_entry(&gg->tops, top, i) if (!kc_vt_is_equal2(&gg->outs, i, &gg->tts, top))
        printf("Verification failed for output %d.\n", i),
        nFailed++;
    if (nFailed == 0)
        printf("Verification succeeded.  ");
}

/*************************************************************
                    AIGER interface
**************************************************************/
static unsigned kc_gg_aiger_read_uint(FILE *pFile)
{
    unsigned x = 0, i = 0;
    unsigned char ch;
    while ((ch = fgetc(pFile)) & 0x80)
        x |= (ch & 0x7f) << (7 * i++);
    return x | (ch << (7 * i));
}

static int *kc_aiger_read(char *pFileName, int *pnObjs, int *pnIns, int *pnLatches, int *pnOuts, int *pnAnds, kc_vt *outs)
{
    int i, Temp, nTotal, nObjs, nIns, nLatches, nOuts, nAnds, *pObjs, *pOuts;
    FILE *pFile = fopen(pFileName, "rb");
    if (pFile == NULL)
    {
        fprintf(stdout, "kc_gg_aiger_read(): Cannot open the output file \"%s\".\n", pFileName);
        return NULL;
    }
    if (fgetc(pFile) != 'a' || fgetc(pFile) != 'i' || fgetc(pFile) != 'g')
    {
        fprintf(stdout, "kc_gg_aiger_read(): Can only read binary AIGER.\n");
        fclose(pFile);
        return NULL;
    }
    if (fscanf(pFile, "%d %d %d %d %d", &nTotal, &nIns, &nLatches, &nOuts, &nAnds) != 5)
    {
        fprintf(stdout, "kc_gg_aiger_read(): Cannot read the header line.\n");
        fclose(pFile);
        return NULL;
    }
    if (nTotal != nIns + nLatches + nAnds)
    {
        fprintf(stdout, "The number of objects does not match.\n");
        fclose(pFile);
        return NULL;
    }
    nObjs = 1 + nIns + 2 * nLatches + nOuts + nAnds;
    pObjs = (int *)calloc(sizeof(int), 2 * nObjs);
    pOuts = (int *)calloc(sizeof(int), 2 * nOuts);
    for (i = 0; i <= nIns + nLatches; i++)
        pObjs[2 * i] = pObjs[2 * i + 1] = KC_GG_NULL;

    // read flop input literals
    for (i = 0; i < nLatches; i++)
    {
        while (fgetc(pFile) != '\n')
            ;
        fscanf(pFile, "%d", &Temp);
        pObjs[2 * (nObjs - nLatches + i) + 0] = Temp;
        pObjs[2 * (nObjs - nLatches + i) + 1] = KC_GG_NULL;
    }
    // read output literals
    for (i = 0; i < nOuts; i++)
    {
        while (fgetc(pFile) != '\n')
            ;
        fscanf(pFile, "%d", &Temp);
        pObjs[2 * (nObjs - nOuts - nLatches + i) + 0] = Temp;
        pObjs[2 * (nObjs - nOuts - nLatches + i) + 1] = Temp;
        pOuts[2 * i + 0] = Temp;
        pOuts[2 * i + 1] = Temp;
    }
    // read the binary part
    while (fgetc(pFile) != '\n')
        ;
    for (i = 0; i < nAnds; i++)
    {
        int uLit = 2 * (1 + nIns + nLatches + i);
        int uLit1 = uLit - kc_gg_aiger_read_uint(pFile);
        int uLit0 = uLit1 - kc_gg_aiger_read_uint(pFile);
        pObjs[uLit + 0] = uLit0;
        pObjs[uLit + 1] = uLit1;
    }
    fclose(pFile);
    if (pnObjs)
        *pnObjs = nObjs;
    if (pnIns)
        *pnIns = nIns;
    if (pnLatches)
        *pnLatches = nLatches;
    if (pnOuts)
        *pnOuts = nOuts;
    if (pnAnds)
        *pnAnds = nAnds;
    return pObjs;
}
static kc_gg *kc_gg_aiger_read(char *pFileName, int fVerbose)
{

    kc_vt Outs, *outs = &Outs;
    int nObjs, nIns, nLatches, nOuts, nAnds, *pObjs = kc_aiger_read(pFileName, &nObjs, &nIns, &nLatches, &nOuts, &nAnds, outs);
    if (pObjs == NULL)
        return NULL;

    kc_gg *p = kc_gg_start(nIns, outs);
    p->cap = 2 * nObjs;
    p->size = 2 * nObjs;
    // p->nRegs  = nLatches;
    for (int i = 0; i < nObjs; i++)
        kc_vi_push(&p->fans, pObjs[i]);
    // p->fans = pObjs;
    if (fVerbose)
        printf("Loaded MiniAIG from the AIGER file \"%s\".\n", pFileName);
    return p;
}

static void kc_aiger_write_uint(FILE *pFile, unsigned x)
{
    unsigned char ch;
    while (x & ~0x7f)
    {
        ch = (x & 0x7f) | 0x80;
        fputc(ch, pFile);
        x >>= 7;
    }
    ch = x;
    fputc(ch, pFile);
}
static void kc_aiger_write(char *pFileName, int *pObjs, int nObjs, int nIns, int nLatches, int nOuts, int nAnds, int *pOuts)
{
    std::string str(pFileName);
    FILE *pFile = fopen(("./outputs/" + str).c_str(), "wb");
    int i;
    if (pFile == NULL)
    {
        fprintf(stdout, "kc_aiger_write(): Cannot open the output file \"%s\".\n", pFileName);
        return;
    }
    fprintf(pFile, "aig %d %d %d %d %d\n", nIns + nLatches + nAnds, nIns, nLatches, nOuts, nAnds);
    for (i = 0; i < nLatches; i++)
        fprintf(pFile, "%d\n", pOuts[nOuts + i]);
    for (i = 0; i < nOuts; i++)
        fprintf(pFile, "%d\n", pOuts[i]);
    for (i = 0; i < nAnds; i++)
    {
        int uLit = 2 * (1 + nIns + nLatches + i);
        int uLit0 = pObjs[uLit + 0];
        int uLit1 = pObjs[uLit + 1];
        kc_aiger_write_uint(pFile, uLit - uLit1);
        kc_aiger_write_uint(pFile, uLit1 - uLit0);
    }
    fprintf(pFile, "c\n");
    fclose(pFile);
}
static void kc_gg_aiger_write(char *pFileName, kc_gg *gg, int fVerbose)
{
    kc_gg *ggNew = kc_gg_dup(gg, 1);
    // kc_gg_print( ggNew, fVerbose );
    kc_aiger_write(pFileName, kc_vi_array(&ggNew->fans), -1, kc_gg_pi_num(ggNew), 0, kc_gg_po_num(ggNew), kc_gg_node_num(ggNew), kc_vi_array(&ggNew->tops));
    if (fVerbose)
        printf("Written graph with %d inputs, %d outputs, and %d and-nodes into AIGER file \"%s\".\n",
               kc_gg_pi_num(ggNew), kc_gg_po_num(ggNew), kc_gg_node_num(ggNew), pFileName);
    kc_gg_stop(ggNew);
}

static void kc_gg_aiger_test(char *pFileNameIn, char *pFileNameOut)
{
    kc_gg *p = kc_gg_aiger_read(pFileNameIn, 1);
    if (p == NULL)
        return;
    printf("Finished reading input file \"%s\".\n", pFileNameIn);
    kc_gg_aiger_write(pFileNameOut, p, 1);
    printf("Finished writing output file \"%s\".\n", pFileNameOut);
    kc_gg_stop(p);
}

/*************************************************************
                  Top level procedures
**************************************************************/

extern "C"
{
    /*
    TO solve the problem I need:
    - read circuit from AIG file and create a graph structure in my environment.
    - implement top_level function that will add nodes nAdds times and verify new circuit and after completion it
    will delete nodes while it is possible (it'll be impossible if we can't delete any node).
    - implement addNode function that will insert node to specific location of graph by resizing graph and moving right
    part of it. To insert node
    */
    // solving one instance of a problem
    int kc_top_level_call(char *fileName, int nAdds, int verbose)
    {
        clock_t clkStart = clock();
        kc_vt Outs, *outs = &Outs;
        int i, j, iChange, iDelete, iCand;
        int start = (2*(gg->nins + 1) + 1);
        kc_gg *gg = kc_gg_aiger_read(fileName, verbose);
        kc_gg *ggReverse;
        
        for (i = 0; i < nAdds;) {
            for (j = start; j < gg->size; j++) {
                iChange = start + Num % (gg->size - start);
                iCand = 2 + Num % ((iChange - 2) - 2);
                ggReverse = gg;
                kc_gg_add_node(gg, iChange, iCand);
                if (!kc_gg_is_correct(gg))
                    kc_gg_reverse(gg, ggReverse);
                else
                    i++;
            }
        }
        while (kc_gg_can_delete_node(gg)) {
            for (j = start; j < gg->size; j++) {
                iDelete = start + Num % (gg->size - start);
                iCand = 2 + Num % ((iChange - 2) - 2);
                ggReverse = gg;
                kc_gg_delete_node(gg, iDelete, iCand);
                if (!kc_gg_is_correct(gg))
                    kc_gg_reverse(gg, ggReverse);
            }
        }
        
        return 1;
    }
}

/*************************************************************
                   main() procedure
**************************************************************/

int main(int argc, char **argv)
{
    char *input = "../rec-synthesis/outputs/80.aig";
    char *output = "80-tested.aig";
    kc_gg_aiger_test(input, output);
}

/*************************************************************
                     End of file
**************************************************************/