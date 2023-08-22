#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <regex>

#define MAX_VARS 16  // the largest allowed number of inputs
#define MAX_SIZE 256 // the number of initially allocated objects
#define KC_GG_NULL (0x7FFFFFFF)
#define Num rand()
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
    // printf("hello index %i value %i\n", k, v->ptr[k]);
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
// static inline void kc_vi_shift(kc_vi *v, int idx, int e)
// {
//     printf("index = %i, e = %i, read = %i ", idx, e, kc_vi_read(v, idx));
//     kc_v
//     // v->ptr[v->size++] = e;
// }
static inline void kc_vi_push(kc_vi *v, int e)
{
    kc_vi_grow(v);
    v->ptr[v->size++] = e;
}
static inline void kc_vi_push_idx(kc_vi *v, int e, int idx)
{
    kc_vi_grow(v);
    v->size++;
    for (int j = v->size - 1; j >= idx; j--)
    {
        v->ptr[j + 1] = v->ptr[j];
    }
    // shift procedure kc_vi_shift(v, idx);
    v->ptr[idx] = e;
}
// delete node
static inline void kc_vi_delete_idx(kc_vi *v, int idx)
{
    v->ptr[idx] = 1;
}
static inline void kc_vi_push2(kc_vi *v, int e1, int e2)
{
    kc_vi_push(v, e1);
    kc_vi_push(v, e2);
}
static inline void kc_vi_push2_idx(kc_vi *v, int idx, int e1, int e2)
{
    printf("e1 = %i, e2 = %i\n", e1, e2);
    v->ptr[idx] = e1;
    v->ptr[idx + 1] = e2;
    // kc_vi_push_idx(v, e1, idx);
    // kc_vi_push_idx(v, e2, idx + 1);
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

static inline void kc_vi_randomized_order(kc_vi *p)
{
    int v;
    for (v = 0; v < p->size; v++)
    {
        int vRand = Num % p->size;
        KC_SWAP(int, p->ptr[vRand], p->ptr[v]);
    }
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

static inline int kc_vt_words(kc_vt *v) { return v->words; }
static inline int kc_vt_size(kc_vt *v) { return v->size; }
static inline kc_uint64 *kc_vt_array(kc_vt *v) { return v->ptr; }
static inline kc_uint64 *kc_vt_read(kc_vt *v, int ttId)
{
    assert(ttId < v->size);
    return v->ptr + ttId * v->words;
}

/*************************************************************
             Boolean operations on truth tables
**************************************************************/

static kc_uint64 s_Truths6[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF0000000};
static kc_uint64 s_Truths6Neg[6] = {
    0x5555555555555555,
    0x3333333333333333,
    0x0F0F0F0F0F0F0F0F,
    0x00FF00FF00FF00FF,
    0x0000FFFF0000FFFF,
    0x00000000FFFFFFFF};

static inline void kc_vt_const0(kc_vt *v, int ttR)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    for (int i = 0; i < v->words; i++)
        pR[i] = 0;
}
static inline void kc_vt_const1(kc_vt *v, int ttR)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    for (int i = 0; i < v->words; i++)
        pR[i] = ~(kc_uint64)0;
}
static inline void kc_vt_var(kc_vt *v, int ttR, int iVar, int nVars)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    if (iVar < 6)
        for (int k = 0; k < v->words; k++)
            pR[k] = s_Truths6[iVar];
    else
        for (int k = 0; k < v->words; k++)
            pR[k] = (k & (1 << (iVar - 6))) ? ~(kc_uint64)0 : 0;
}
static inline void kc_vt_dup(kc_vt *v, int ttR, int ttA)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    kc_uint64 *pA = kc_vt_read(v, ttA);
    for (int i = 0; i < v->words; i++)
        pR[i] = pA[i];
}
static inline void kc_vt_inv(kc_vt *v, int ttR, int ttA)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    kc_uint64 *pA = kc_vt_read(v, ttA);
    for (int i = 0; i < v->words; i++)
        pR[i] = ~pA[i];
}
static inline void kc_vt_and(kc_vt *v, int ttR, int ttA, int ttB)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    for (int i = 0; i < v->words; i++)
        pR[i] = pA[i] & pB[i];
}
static inline void kc_vt_or_xor(kc_vt *v, int ttR, int ttA, int ttB)
{
    kc_uint64 *pR = kc_vt_read(v, ttR);
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    for (int i = 0; i < v->words; i++)
        pR[i] |= pA[i] ^ pB[i];
}

static inline int kc_vt_is_equal(kc_vt *v, int ttA, int ttB)
{
    kc_uint64 *pA = kc_vt_read(v, ttA);
    kc_uint64 *pB = kc_vt_read(v, ttB);
    for (int i = 0; i < v->words; i++)
        if (pA[i] != pB[i])
            return 0;
    return 1;
}
static inline int kc_vt_is_equal2(kc_vt *vA, int ttA, kc_vt *vB, int ttB)
{
    kc_uint64 *pA = kc_vt_read(vA, ttA);
    kc_uint64 *pB = kc_vt_read(vB, ttB);
    assert(vA->words == vB->words);
    for (int i = 0; i < vA->words; i++)
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
               Initialization of truth tables
**************************************************************/

static inline void kc_vt_start(kc_vt *v, int cap, int words)
{
    v->size = 0;
    v->cap = cap;
    v->words = words;
    v->ptr = (kc_uint64 *)malloc(8 * v->cap * v->words);
}
static inline void kc_vt_start_truth(kc_vt *v, int cap, int nvars)
{
    assert(cap > 2 * (1 + nvars));
    v->size = cap;
    v->cap = cap;
    v->words = kc_truth_word_num(nvars);
    v->ptr = (kc_uint64 *)malloc(8 * v->words * v->cap);
    kc_vt_const0(v, 0);
    kc_vt_const1(v, 1);
    for (int ivar = 0; ivar < nvars; ivar++)
    {
        kc_vt_var(v, 2 * (1 + ivar) + 0, ivar, nvars);
        kc_vt_inv(v, 2 * (1 + ivar) + 1, 2 * (1 + ivar) + 0);
        // printf("lit = %2d  ", ivar + 2);
        // kc_vt_print(v, ivar + 2);
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
                 Gate graph data structure
**************************************************************/

typedef struct kc_gg_
{
    int cap;   // the number of objects allocated
    int size;  // the number of objects currently present, including const0, primary inputs, and internal nodes if any
    int nins;  // the number of primary inputs
    int nouts; // the number of primary outputs
    int tid;   // the current traversal ID

    kc_vi tids;  // the last visited tranversal ID of each object
    kc_vi fans;  // the fanins of objects
    kc_vt funcs; // the functions of objects
} kc_gg;

// reading fanins
static inline int kc_gg_fanin(kc_gg *p, int v, int n)
{
    assert(n == 0 || n == 1);
    return kc_vi_read(&p->fans, 2 * v + n);
}

static inline int kc_gg_pi_num(kc_gg *p) { return p->nins; }
static inline int kc_gg_po_num(kc_gg *p) { return p->nouts; }
static inline int kc_gg_obj_num(kc_gg *p) { return p->size; }
static inline int kc_gg_node_num(kc_gg *p) { return p->size - 1 - p->nins - p->nouts; }

static inline int kc_gg_is_const0(kc_gg *p, int v) { return v == 0; }
static inline int kc_gg_is_pi(kc_gg *p, int v) { return kc_gg_fanin(p, v, 0) == KC_GG_NULL && kc_gg_fanin(p, v, 1) == KC_GG_NULL && v > 0; }
static inline int kc_gg_is_po(kc_gg *p, int v) { return kc_gg_fanin(p, v, 0) != KC_GG_NULL && kc_gg_fanin(p, v, 1) == KC_GG_NULL; }
static inline int kc_gg_is_node(kc_gg *p, int v) { return kc_gg_fanin(p, v, 0) != KC_GG_NULL && kc_gg_fanin(p, v, 1) != KC_GG_NULL; }

static inline int kc_gg_is_empty(kc_gg *p, int v) { return kc_gg_fanin(p, v, 0) == -1; }

// managing traversal IDs
static inline int kc_gg_tid_increment(kc_gg *p)
{
    assert(p->tid < 0x7FFFFFFF);
    return p->tid++;
}

// shift right part array
// static inline void kc_gg_shift(kc_gg *gg, int idx)
// {
//     int lit0, lit1;
//     for (int i = idx + 1; i < gg->size; i++)
//     {
//         lit0 = kc_gg_fanin(gg, i, 0);
//         lit1 = kc_gg_fanin(gg, i, 1);
//         if (kc_gg_is_po(gg, i))
//             kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
//         else
//         {
//             if (i == idx + 1)
//             {
//                 kc_vi_write(&gg->fans, 2 * i, 2 * (i - 1));
//                 if (!kc_gg_is_pi(gg, kc_l2v(lit1)) && (lit1 > 2 * i + 1))
//                     kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
//             }
//             else
//             {
//                 if (!kc_gg_is_pi(gg, kc_l2v(lit0)))
//                     kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
//                 if (!kc_gg_is_pi(gg, kc_l2v(lit1)))
//                     kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
//                 if (lit0 > 2 * i + 1)
//                     kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
//                 if (lit1 > 2 * i + 1)
//                     kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
//             }
//         }
//     }
// }

// adds one node to the AIG
static inline int kc_gg_add_obj(kc_gg *p, int lit0, int lit1)
{
    int ilast = p->size++;
    kc_vi_push2(&p->tids, 0, 0);
    if (lit0 < lit1)
        kc_vi_push2(&p->fans, lit0, lit1);
    else
        kc_vi_push2(&p->fans, lit1, lit0);
    // if (!(lit0 == -1 || lit1 == -1))
    //     kc_vi_push2(&p->edges, kc_v2l(ilast, 0), kc_v2l(ilast, 1));

    p->nins += kc_gg_is_pi(p, ilast);
    p->nouts += kc_gg_is_po(p, ilast);
    return 2 * ilast;
}

// insert one node at idx to the AIG
// static inline void kc_gg_insert_obj(kc_gg *p, int idx, int lit, int ratio)
// {
//     // p->size++;
//     int i;
//     for (i = 1; i < ratio; i++)
//     {
//         printf("idx = %i\n", kc_l2v(idx));
//         if (!kc_gg_is_node(p, kc_l2v(idx) - i))
//             break;
//     }
//     printf("(%i, %i) is not a node\n", kc_gg_fanin(p, kc_l2v(idx) - i, 0), kc_gg_fanin(p, kc_l2v(idx) - i, 1));
//     // kc_vi_push2_idx(&p->fans, idx, lit);
//     kc_vi_push2_idx(&p->tids, 2 * (kc_l2v(idx) - i), 0, 0);
//     kc_vi_push2_idx(&p->fans, 2 * (kc_l2v(idx) - i), kc_gg_fanin(p, kc_l2v(idx), kc_l2c(idx)), lit);
//     // kc_gg_shift(p, idx / 2);
//     p->nins += kc_gg_is_pi(p, kc_l2v(idx) - i);
//     p->nouts += kc_gg_is_po(p, kc_l2v(idx) - i);
// }

// delete one node at idx to the AIG
static inline void kc_gg_delete_obj(kc_gg *p, int idx)
{
    p->nins -= kc_gg_is_pi(p, idx / 2);
    p->nouts -= kc_gg_is_po(p, idx / 2);
    kc_vi_delete_idx(&p->tids, idx);
    kc_vi_delete_idx(&p->fans, idx);
}

// constructor and destructor
static inline kc_gg *kc_gg_start(int cap)
{
    kc_gg *gg = (kc_gg *)calloc(sizeof(kc_gg), 1);
    gg->cap = cap;
    gg->tid = 1;
    kc_vi_start(&gg->tids, 2 * gg->cap);
    kc_vi_start(&gg->fans, 2 * gg->cap);
    return gg;
}
static inline void kc_gg_stop(kc_gg *gg)
{
    if (gg == NULL)
        return;
    kc_vi_stop(&gg->tids);
    kc_vi_stop(&gg->fans);
    kc_vt_stop(&gg->funcs);
    free(gg);
}
static inline void kc_gg_simulate(kc_gg *gg)
{
    kc_vt *v = &gg->funcs;
    kc_vt_start_truth(v, 2 * gg->cap, gg->nins);
    for (int i = 0; i < gg->size; i++)
        if (kc_gg_is_node(gg, i))
        {
            kc_vt_and(v, 2 * i + 0, kc_gg_fanin(gg, i, 0), kc_gg_fanin(gg, i, 1));
            kc_vt_inv(v, 2 * i + 1, 2 * i + 0);
        }
    // we do not create truth tables for primary outputs
    // because we will access their functions by looking up
    // the truth tables for the fanin literals
}

static inline bool kc_gg_verify(kc_gg *gg1, kc_gg *gg2)
{
    int i, nFails = 0;
    assert(kc_gg_po_num(gg1) == kc_gg_po_num(gg2));
    // confirm that primary outputs are the last objects in each gg
    for (i = kc_gg_obj_num(gg1) - kc_gg_po_num(gg1); i < kc_gg_obj_num(gg1); i++)
        assert(kc_gg_is_po(gg1, i));
    for (i = kc_gg_obj_num(gg2) - kc_gg_po_num(gg2); i < kc_gg_obj_num(gg2); i++)
        assert(kc_gg_is_po(gg2, i));
    // compare output functions
    for (i = 0; i < kc_gg_po_num(gg1); i++)
    {
        int obj1 = kc_gg_obj_num(gg1) - kc_gg_po_num(gg1) + i;
        int obj2 = kc_gg_obj_num(gg2) - kc_gg_po_num(gg2) + i;
        if (!kc_vt_is_equal2(&gg1->funcs, kc_gg_fanin(gg1, obj1, 0),
                             &gg2->funcs, kc_gg_fanin(gg2, obj2, 0)))
            printf("Verification failed for output %d.", i),
                nFails++;
    }
    if (nFails == 0)
    {
        printf("Verification successful!\n");
        return 1;
    }
    else
    {
        printf("Verification failed for %d outputs.\n", nFails);
        return 0;
    }
}

// printing the graph
void kc_gg_print_lit(kc_gg *gg, int lit)
{
    if (lit == -1)
        return;
    assert(lit >= 0);
    assert(!kc_gg_is_po(gg, kc_l2v(lit)));
    if (lit < 2)
        printf("%d", lit);
    else if (kc_gg_is_pi(gg, kc_l2v(lit)))
        printf("%s%c", kc_l2c(lit) ? "~" : "", (char)('a' - 1 + kc_l2v(lit)));
    else
        printf("%s%02d", kc_l2c(lit) ? "~n" : "n", kc_l2v(lit));
}
void kc_gg_print(kc_gg *gg, int verbose)
{
    int i, nIns = 0, nOuts = 0, nAnds = 0, nInvalid = 0;
    for (i = 0; i < gg->size; i++)
    {
        if (!(kc_gg_fanin(gg, i, 0) == -1 || kc_gg_fanin(gg, i, 1) == -1))
        {
            printf("Obj%02d : ", i);
            if (kc_gg_is_const0(gg, i))
                printf("const0");
            else if (kc_gg_is_pi(gg, i))
                printf("i%02d = %c", nIns, (char)('a' - 1 + i)), nIns++;
            else if (kc_gg_is_po(gg, i))
                printf("o%02d = ", nOuts), kc_gg_print_lit(gg, kc_gg_fanin(gg, i, 0)), nOuts++;
            else // internal node
                printf("n%02d = ", i), kc_gg_print_lit(gg, kc_gg_fanin(gg, i, 0)), printf(" & "), kc_gg_print_lit(gg, kc_gg_fanin(gg, i, 1)), nAnds++;
            printf("\n");
        }
        else
            nInvalid++;
    }
    assert(nIns == kc_gg_pi_num(gg));
    assert(nOuts == kc_gg_po_num(gg));
    assert(nAnds == kc_gg_node_num(gg) - nInvalid);
    printf("The graph contains %d inputs, %d outputs, and %d internal and-nodes.\n", nIns, nOuts, nAnds);
}

int kc_gg_check_structurally_similar(kc_gg *gg, int lit1, int lit2)
{
    for (int i = 1 + gg->nins; i < gg->size - gg->nouts; i++)
        if (kc_gg_fanin(gg, i, 0) == lit1 && kc_gg_fanin(gg, i, 1) == lit2)
            return kc_v2l(i, 0);
    return -1;
}

// duplicates AIG
kc_gg *kc_gg_dup(kc_gg *gg)
{
    kc_gg *ggNew = kc_gg_start(gg->cap);
    int *pCopy = (int *)malloc(sizeof(int) * 2 * gg->size);
    for (int i = 0; i < gg->size; i++)
    {
        if (kc_gg_is_empty(gg, i))
            continue;
        if (kc_gg_is_const0(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
        else if (kc_gg_is_pi(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
        else if (kc_gg_is_po(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, i, 0)], KC_GG_NULL);
        else if (pCopy[kc_gg_fanin(gg, i, 0)] == 0 || pCopy[kc_gg_fanin(gg, i, 1)] == 0)
            pCopy[2 * i] = 0;
        else if (pCopy[kc_gg_fanin(gg, i, 0)] == 1)
            pCopy[2 * i] = pCopy[kc_gg_fanin(gg, i, 1)];
        else if (pCopy[kc_gg_fanin(gg, i, 1)] == 1)
            pCopy[2 * i] = pCopy[kc_gg_fanin(gg, i, 0)];
        else
        {
            int lit = (kc_gg_check_structurally_similar(ggNew, pCopy[kc_gg_fanin(gg, i, 0)], pCopy[kc_gg_fanin(gg, i, 1)]));
            if (lit == -1)
                pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, i, 0)], pCopy[kc_gg_fanin(gg, i, 1)]);
            else
                pCopy[2 * i] = lit;
        }
        pCopy[2 * i + 1] = kc_lnot(pCopy[2 * i]);
    }
    free(pCopy);
    return ggNew;
}

// extend AIG by inserting emty nodes (-1, -1)
kc_gg *kc_gg_extend(kc_gg *gg, int ratio)
{
    kc_gg *ggNew = kc_gg_start(5 * (ratio + 1) * gg->cap);
    int size = (((gg->nins + 1) + (gg->size - gg->nins - 1) * (ratio + 1)));
    int *pCopy = (int *)malloc(sizeof(int) * 2 * size);
    int count = 1;
    for (int i = 0; i < gg->nins + 1; i++)
    {
        if (kc_gg_is_const0(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
        else if (kc_gg_is_pi(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
    }
    for (int i = gg->nins + 1; i < size; i++)
    {
        if (count % (ratio + 1) == 0)
        {
            if (kc_gg_is_po(gg, (i - ratio * (count / (ratio + 1)))))
            {
                if (kc_gg_is_pi(gg, kc_l2v(pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)])))
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)], KC_GG_NULL);
                else
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, 2 * (pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)] / 2 + ratio * ((count / (ratio + 1)) - 1)), KC_GG_NULL);
            }
            else
            {
                if (kc_gg_is_pi(gg, kc_l2v(pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)])) && kc_gg_is_pi(gg, kc_l2v(pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)])))
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)], pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)]);
                else if (kc_gg_is_pi(gg, kc_l2v(pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)])))
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)], 2 * (pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)] / 2 + ratio * ((count / (ratio + 1)) - 1)));
                else if (kc_gg_is_pi(gg, kc_l2v(pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)])))
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, 2 * (pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)] / 2 + ratio * ((count / (ratio + 1)) - 1)), pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)]);
                else
                    pCopy[2 * i] = kc_gg_add_obj(ggNew, 2 * (pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 0)] / 2 + ratio * ((count / (ratio + 1)) - 1)), 2 * (pCopy[kc_gg_fanin(gg, (i - ratio * (count / (ratio + 1))), 1)] / 2 + ratio * ((count / (ratio + 1)) - 1)));
            }
        }
        else
            pCopy[2 * i] = kc_gg_add_obj(ggNew, -1, 1);
        count++;
        pCopy[2 * i + 1] = kc_lnot(pCopy[2 * i]);
    }
    free(pCopy);
    return ggNew;
}

/*************************************************************
                    new extension procedure
**************************************************************/

// this procedure transforms the old AIG literal i
// into a new AIG literal from the new AIG that is extended "ratio" times
static inline int kc_gg_trans_lit(int i, int ratio)
{
    return kc_v2l(kc_l2v(i) * ratio, kc_l2c(i));
}

// this procedure extends gg to have several times more nodes
// (for example, when ratio=3, the new gg has 3x more nodes)
// each original node (lit0, lit1) is followed by two empty nodes (-1, -1)
static inline kc_gg *kc_gg_extend2(kc_gg *gg, int ratio)
{
    kc_gg *ggNew = kc_gg_start(gg->size * ratio);
    // fill up the fanin array with value -1
    kc_vi_fill(&ggNew->fans, 2 * gg->size * ratio, -1);
    kc_vi_fill(&ggNew->tids, 2 * gg->size * ratio, 0);
    ggNew->size = gg->size * ratio;
    ggNew->nins = gg->nins;
    ggNew->nouts = gg->nouts;
    // since we do not grow these arrays, we can access entries directly
    int *pFansOld = kc_vi_array(&gg->fans);
    int *pFansNew = kc_vi_array(&ggNew->fans);
    // remap old literals into new literals while transforming them
    for (int i = 0; i < 2 * gg->size; i++)
        if (pFansOld[i] == KC_GG_NULL)
            pFansNew[kc_gg_trans_lit(i, ratio)] = KC_GG_NULL;
        else
            pFansNew[kc_gg_trans_lit(i, ratio)] = kc_gg_trans_lit(pFansOld[i], ratio);
    return ggNew;
}

static inline void kc_gg_extend2_test(kc_gg *gg, int ratio)
{
    kc_gg *ggNew = kc_gg_extend2(gg, ratio);
    kc_gg *ggOld = kc_gg_dup(ggNew);
    // get the fanin arrays
    kc_vi *viOldOld = &gg->fans;
    kc_vi *viNewOld = &ggOld->fans;
    // check that the literal arrays of gg and ggOld are the same
    assert(viOldOld->size == viNewOld->size);
    if (memcmp(viOldOld->ptr, viNewOld->ptr, sizeof(int) * viNewOld->size) == 0)
        printf("Verification passed.\n");
    else
        printf("Verification failed.\n");
}

/*************************************************************
                inserting / removing nodes
**************************************************************/

// iIndex is the index in the array "&gg->fans" of the edge where a new node is added
// iNewLit is the second literal of the new node (iNewLit == 1 preserves functionality)
static inline int kc_gg_insert_node(kc_gg *gg, int iIndex, int iNewLit)
{

    int iNode = kc_l2v(iIndex); // the node whose edge is being updated

    int iPrev1 = iNode - 1; // the previous node
    int iPrev2 = iNode - 2; // the node before the previous node
    int iPrev = -1;
    assert(!kc_gg_is_empty(gg, iNode));
    // one of the two previous nodes should be empty
    if (kc_gg_is_empty(gg, iPrev1))
        iPrev = iPrev1;
    else if (kc_gg_is_empty(gg, iPrev2))
        iPrev = iPrev2;
    else
        return -1;
    assert(iPrev != -1);

    if (kc_gg_is_po(gg, iNode) && kc_l2c(iIndex) == 1)
    {
        // transform iPrev into a new node having the same edge and iNewLit
        kc_vi_write(&gg->fans, kc_v2l(iPrev, 0), kc_vi_read(&gg->fans, iIndex - 1));
        kc_vi_write(&gg->fans, kc_v2l(iPrev, 1), iNewLit);
        // redirect the edge to point to the new node
        kc_vi_write(&gg->fans, iIndex - 1, kc_v2l(iPrev, 0));
    }
    else
    {
        // transform iPrev into a new node having the same edge and iNewLit
        kc_vi_write(&gg->fans, kc_v2l(iPrev, 0), kc_vi_read(&gg->fans, iIndex));
        kc_vi_write(&gg->fans, kc_v2l(iPrev, 1), iNewLit);
        // redirect the edge to point to the new node
        kc_vi_write(&gg->fans, iIndex, kc_v2l(iPrev, 0));
    }
    return iPrev;
}
static inline kc_vi *kc_gg_edges_indices(kc_gg *gg, int ratio)
{
    kc_vi *edges = (kc_vi *)calloc(sizeof(kc_vi), 1);
    kc_vi_start(edges, (gg->size - gg->nins - gg->nouts));

    for (int i = 2 * ratio * (gg->nins + 1); i < 2 * (gg->size - gg->nouts * ratio); i++)
    {
        if (!kc_gg_is_empty(gg, kc_l2v(i)))
            kc_vi_push(edges, i);
        // printf("edge: %i and (%i, %i)\n", i, kc_gg_fanin(gg, kc_l2v(i), 0), kc_gg_fanin(gg, kc_l2v(i), 1));
    }
    return edges;
}
// iIndex is the index in the array "&gg->fans" of the edge to be removed
static inline void kc_gg_remove_edge(kc_gg *gg, int iIndex)
{
    // printf("index %i\n", iIndex);
    kc_vi_write(&gg->fans, iIndex, 1);
    // printf("hello\n");
}

static inline void kc_gg_reverse_node(kc_gg *gg, int iNode, int iChange)
{
    // printf("iNode = %i, index at iNode")
    if (kc_gg_is_po(gg, kc_l2v(iChange)) && kc_l2c(iChange) == 1)
        kc_vi_write(&gg->fans, iChange - 1, kc_gg_fanin(gg, iNode, 0));
    else
        kc_vi_write(&gg->fans, iChange, kc_gg_fanin(gg, iNode, 0));
    kc_vi_write(&gg->fans, kc_v2l(iNode, 0), -1);
    kc_vi_write(&gg->fans, kc_v2l(iNode, 1), -1);
}

static inline void kc_gg_reverse_edge(kc_gg *gg, int iEdge, int val)
{
    kc_vi_write(&gg->fans, iEdge, val);
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

static int *kc_aiger_read(char *pFileName, int *pnObjs, int *pnIns, int *pnLatches, int *pnOuts, int *pnAnds)
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
    for (i = 0; i <= nIns + nLatches; i++)
        pObjs[2 * i] = pObjs[2 * i + 1] = KC_GG_NULL;

    // read flop input literals
    for (i = 0; i < nLatches; i++)
    {
        while (fgetc(pFile) != '\n')
            ;
        int value = fscanf(pFile, "%d", &Temp);
        assert(value == 1);
        pObjs[2 * (nObjs - nLatches + i) + 0] = Temp;
        pObjs[2 * (nObjs - nLatches + i) + 1] = KC_GG_NULL;
    }
    // read output literals
    for (i = 0; i < nOuts; i++)
    {
        while (fgetc(pFile) != '\n')
            ;
        int value = fscanf(pFile, "%d", &Temp);
        assert(value == 1);
        pObjs[2 * (nObjs - nOuts - nLatches + i) + 0] = Temp;
        pObjs[2 * (nObjs - nOuts - nLatches + i) + 1] = KC_GG_NULL;
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
static kc_gg *kc_gg_aiger_read(char *pFileName, int fVerbose, int ratio)
{
    int i, nObjs, nIns, nLatches, nOuts, nAnds, *pObjs = kc_aiger_read(pFileName, &nObjs, &nIns, &nLatches, &nOuts, &nAnds);
    if (pObjs == NULL)
        return NULL;
    kc_gg *p = kc_gg_start((ratio + 1) * 3 * nObjs);
    printf("num of obj %i\n", nObjs);
    for (i = 0; i < nObjs; i++)
        kc_gg_add_obj(p, pObjs[2 * i + 0], pObjs[2 * i + 1]);

    if (fVerbose)
        printf("Loaded AIG from the AIGER file \"%s\".\n", pFileName);
    kc_gg_print(p, fVerbose);
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
static void kc_aiger_write(char *pFileName, int *pObjs, int nObjs, int nIns, int nLatches, int nOuts, int nAnds)
{
    FILE *pFile = fopen(pFileName, "wb");
    int i;
    if (pFile == NULL)
    {
        fprintf(stdout, "kc_aiger_write(): Cannot open the output file \"%s\".\n", pFileName);
        return;
    }
    // make sure the last objects are latches
    for (i = 0; i < nLatches; i++)
        assert(pObjs[2 * (nObjs - nLatches + i) + 1] == KC_GG_NULL);
    // make sure the objects before latches are outputs
    for (i = 0; i < nOuts; i++)
        assert(pObjs[2 * (nObjs - nOuts - nLatches + i) + 1] == KC_GG_NULL);

    fprintf(pFile, "aig %d %d %d %d %d\n", nIns + nLatches + nAnds, nIns, nLatches, nOuts, nAnds);
    for (i = 0; i < nLatches; i++)
        fprintf(pFile, "%d\n", pObjs[2 * (nObjs - nLatches + i) + 0]);
    for (i = 0; i < nOuts; i++)
        fprintf(pFile, "%d\n", pObjs[2 * (nObjs - nOuts - nLatches + i) + 0]);
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
    kc_gg *ggNew = kc_gg_dup(gg);
    kc_gg_print(ggNew, fVerbose);
    kc_aiger_write(pFileName, kc_vi_array(&ggNew->fans), kc_vi_size(&ggNew->fans) / 2, kc_gg_pi_num(ggNew), 0, kc_gg_po_num(ggNew), kc_gg_node_num(ggNew));
    if (fVerbose)
        printf("Written graph with %d inputs, %d outputs, and %d and-nodes into AIGER file \"%s\".\n",
               kc_gg_pi_num(ggNew), kc_gg_po_num(ggNew), kc_gg_node_num(ggNew), pFileName);
    kc_gg_stop(ggNew);
}

static void kc_gg_aiger_test(char *pFileNameIn, char *pFileNameOut, int ratio)
{
    kc_gg *p = kc_gg_aiger_read(pFileNameIn, 1, ratio);
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
    int kc_top_level_call(char *pFileNameIn, int verbose, int ratio, int nadds)
    {
        clock_t clkStart = clock();
        int iChange, iDelete, iCand;
        kc_gg *ggOrig = kc_gg_aiger_read(pFileNameIn, 1, ratio);
        kc_gg_simulate(ggOrig);
        if (ggOrig == NULL)
            return 0;
        printf("Finished reading input file \"%s\".\n", pFileNameIn);

        kc_gg *gg = kc_gg_extend2(ggOrig, ratio);

        kc_vi *edgesToInsert = kc_gg_edges_indices(gg, ratio);
        kc_vi_randomized_order(edgesToInsert);
        for (int i = 0; i < edgesToInsert->size; i++)
            printf("%i ", edgesToInsert->ptr[i]);
        printf("\n\n");
        assert(nadds <= edgesToInsert->size);
        kc_gg *ggNew;
        // printf("\n\n Starting insertion\n\n");
        int start = 2 * ratio * (gg->nins + 1);
        for (int i = 0; i < nadds; i++)
        {
            do
            {
                iChange = start + (Num % (2 * gg->size - 1 - start));
            } while (kc_gg_is_empty(gg, kc_l2v(iChange)));
            iCand = 2 * ratio + Num % ((edgesToInsert->ptr[i] - 2) - 2);
            printf("Before\n");
            for (int j = 0; j < gg->size; j++)
            {
                printf("(%i, %i) ", kc_gg_fanin(gg, j, 0), kc_gg_fanin(gg, j, 1));
            }
            printf("\n");

            int iNode = kc_gg_insert_node(gg, edgesToInsert->ptr[i], iCand);
            printf("After\n");
            // printf("index = %i, val = (%i, %i)\n", iChange, kc_gg_fanin(gg, kc_l2v(iChange), 0), kc_gg_fanin(gg, kc_l2v(iChange), 1));
            for (int j = 0; j < gg->size; j++)
            {
                printf("(%i, %i) ", kc_gg_fanin(gg, j, 0), kc_gg_fanin(gg, j, 1));
            }
            printf("\n");
            // printf("\n index = %i\n", iNode);

            ggNew = kc_gg_dup(gg);
            kc_gg_simulate(ggNew);

            if (!kc_gg_verify(ggNew, ggOrig))
                kc_gg_reverse_node(gg, iNode, edgesToInsert->ptr[i]);
        }
        printf("\n\n Finished insertion\n\n");
        kc_gg *ggReverse = kc_gg_dup(gg);
        // kc_gg_print(ggReverse, 1);
        // printf("\n\n Starting deletion\n\n");
        kc_vi *edges = kc_gg_edges_indices(ggReverse, 1);
        kc_vi_randomized_order(edges);
        for (int i = 0; i < edges->size; i++)
        {
            // printf("Before\n");
            // for (int j = 0; j < ggReverse->size; j++)
            //     printf("(%i, %i) ", kc_gg_fanin(ggReverse, j, 0), kc_gg_fanin(ggReverse, j, 1));
            // printf("\n");

            int deletedVal = kc_gg_fanin(ggReverse, kc_l2v(edges->ptr[i]), kc_l2c(edges->ptr[i]));
            kc_gg_remove_edge(ggReverse, edges->ptr[i]);

            // printf("After\n");
            // for (int j = 0; j < ggReverse->size; j++)
            //     printf("(%i, %i) ", kc_gg_fanin(ggReverse, j, 0), kc_gg_fanin(ggReverse, j, 1));
            // printf("\n");

            kc_gg_simulate(ggReverse);
            if (!kc_gg_verify(ggReverse, ggOrig))
                kc_gg_reverse_edge(ggReverse, edges->ptr[i], deletedVal);
        }
        printf("\nFinished reduction\n\n");
        kc_gg *ggFinal = kc_gg_dup(ggReverse);
        kc_gg_print(ggFinal, 1);
        printf("Time =%6.2f sec\n", (float)(clock() - clkStart) / CLOCKS_PER_SEC);
        return 1;
    }
}

/*************************************************************
                   main() procedure
**************************************************************/

int main(int argc, char **argv)
{

    char *input = (char *)"../rec-synthesis/outputs/test.aig";
    char *output = (char *)"test_out.aig";

    // kc_gg_aiger_test(input, output);

    if (argc == 1)
    {
        printf("usage:  %s <int> [-v] <string>\n", argv[0]);
        printf("        this program synthesized circuits from truth tables\n");
        printf("     <int> : how many nodes to add before trying to delete\n");
        printf("        -v : enables verbose output\n");
        printf("  <string> : a truth table in hex notation or a file name\n");
        return 1;
    }
    else
    {
        int nAdds = 0;
        int verbose = 0;
        kc_top_level_call(argv[argc - 1], 1, 3, 10);

        // kc_gg *ggOrig = kc_gg_aiger_read(argv[argc - 1], 1, 0);
        // kc_gg_extend2_test( ggOrig, 3 );
        // kc_gg_stop( ggOrig );
    }
}

/*************************************************************
                     End of file
**************************************************************/
