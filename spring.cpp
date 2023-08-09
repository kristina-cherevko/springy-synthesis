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
        v->ptr[j + 1] = v->ptr[j];
    // shift procedure kc_vi_shift(v, idx);
    v->ptr[idx] = e;
}
static inline void kc_vi_push2(kc_vi *v, int e1, int e2)
{
    kc_vi_push(v, e1);
    kc_vi_push(v, e2);
}
static inline void kc_vi_push2_idx(kc_vi *v, int e1, int e2, int idx)
{
    kc_vi_push_idx(v, e1, idx);
    kc_vi_push_idx(v, e2, idx + 1);
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
        printf("lit = %2d  ", ivar + 2);
        kc_vt_print(v, ivar + 2);
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

// managing traversal IDs
static inline int kc_gg_tid_increment(kc_gg *p)
{
    assert(p->tid < 0x7FFFFFFF);
    return p->tid++;
}

// shift right part array
static inline void kc_gg_shift(kc_gg *gg, int idx)
{
    int lit0, lit1;
    for (int i = idx + 1; i < gg->size; i++)
    {
        lit0 = kc_gg_fanin(gg, i, 0);
        lit1 = kc_gg_fanin(gg, i, 1);
        if (i == idx + 1)
        {
            kc_vi_write(&gg->fans, 2 * i, 2 * (i - 1));
            // kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
        }
        else
        {
            if (kc_gg_is_po(gg, i))
                kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
            else
            {
                if (!kc_gg_is_pi(gg, kc_l2v(lit0)))
                    kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
                if (!kc_gg_is_pi(gg, kc_l2v(lit1)))
                    kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
                if (lit0 > 2 * i)
                    kc_vi_write(&gg->fans, 2 * i, lit0 + 2);
                if (lit1 > 2 * i)
                    kc_vi_write(&gg->fans, 2 * i + 1, lit1 + 2);
            }
            // printf("hello - ");
        }
        printf("(%i, %i)\n", kc_gg_fanin(gg, i, 0), kc_gg_fanin(gg, i, 1));
    }
}

// adds one node to the AIG
static inline int kc_gg_add_obj(kc_gg *p, int lit0, int lit1)
{
    int ilast = p->size++;
    kc_vi_push2(&p->tids, 0, 0);
    kc_vi_push2(&p->fans, lit0, lit1);
    p->nins += kc_gg_is_pi(p, ilast);
    p->nouts += kc_gg_is_po(p, ilast);
    return 2 * ilast;
}

// insert one node at idx to the AIG
static inline void kc_gg_insert_obj(kc_gg *p, int idx, int lit0, int lit1)
{
    int ilast = p->size++;
    kc_vi_push2_idx(&p->tids, 0, 0, idx);
    kc_vi_push2_idx(&p->fans, lit0, lit1, idx);
    kc_gg_shift(p, idx / 2);
    p->nins += kc_gg_is_pi(p, ilast);
    p->nouts += kc_gg_is_po(p, ilast);
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
static inline void kc_gg_verify(kc_gg *gg1, kc_gg *gg2)
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
            printf("Verification failed for output %d.", i), nFails++;
    }
    if (nFails == 0)
        printf("Verification successful!\n");
    else
        printf("Verification failed for %d outputs.\n", nFails);
}

// printing the graph
void kc_gg_print_lit(kc_gg *gg, int lit)
{
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
    int i, nIns = 0, nOuts = 0, nAnds = 0;
    for (i = 0; i < gg->size; i++)
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
    assert(nIns == kc_gg_pi_num(gg));
    assert(nOuts == kc_gg_po_num(gg));
    assert(nAnds == kc_gg_node_num(gg));
    printf("The graph contains %d inputs, %d outputs, and %d internal and-nodes.\n", nIns, nOuts, nAnds);
}

// duplicates AIG
kc_gg *kc_gg_dup(kc_gg *gg)
{
    kc_gg *ggNew = kc_gg_start(gg->cap);
    int *pCopy = (int *)malloc(sizeof(int) * 2 * gg->size);
    for (int i = 0; i < gg->size; i++)
    {
        if (kc_gg_is_const0(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
        else if (kc_gg_is_pi(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, KC_GG_NULL, KC_GG_NULL);
        else if (kc_gg_is_po(gg, i))
            pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, i, 0)], KC_GG_NULL);
        else // internal node
            pCopy[2 * i] = kc_gg_add_obj(ggNew, pCopy[kc_gg_fanin(gg, i, 0)], pCopy[kc_gg_fanin(gg, i, 1)]);
        pCopy[2 * i + 1] = kc_lnot(pCopy[2 * i]);
    }
    free(pCopy);
    return ggNew;
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
static kc_gg *kc_gg_aiger_read(char *pFileName, int fVerbose)
{
    int i, nObjs, nIns, nLatches, nOuts, nAnds, *pObjs = kc_aiger_read(pFileName, &nObjs, &nIns, &nLatches, &nOuts, &nAnds);
    if (pObjs == NULL)
        return NULL;
    kc_gg *p = kc_gg_start(3 * nObjs);
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
    part of it.
    */
    // solving one instance of a problem
    int kc_top_level_call(char *pFileNameIn, int nadds, int verbose)
    {
        clock_t clkStart = clock();
        int iChange, iDelete, iCand;
        kc_gg *gg = kc_gg_aiger_read(pFileNameIn, 1);
        kc_gg *ggCopy;
        if (gg == NULL)
            return 0;
        printf("Finished reading input file \"%s\".\n", pFileNameIn);
        int start = (gg->nins + 1);
        for (int j = 0; j < gg->size; j++)
        {
            printf("(%i, %i) ", kc_gg_fanin(gg, j, 0), kc_gg_fanin(gg, j, 1));
        }
        printf("\n\n");
        for (int i = 0; i < nadds; i++)
        {
            iChange = start + (Num % (gg->size - start));
            iCand = 2 + Num % ((2 * iChange - 2) - 2);
            ggCopy = kc_gg_dup(gg);
            printf("(%i, %i)\n", kc_gg_fanin(gg, iChange, 0), iCand);
            kc_gg_insert_obj(gg, 2 * iChange, kc_gg_fanin(gg, iChange, 0), iCand);
            for (int j = 0; j < gg->size; j++)
            {
                printf("(%i, %i) ", kc_gg_fanin(gg, j, 0), kc_gg_fanin(gg, j, 1));
            }
            printf("\n\n");
            // kc_gg_simulate(gg);
        }

        /* pseudocode for the whole procedure

            int start = (2 * (gg->nins + 1) + 1);
            kc_gg *gg = kc_gg_aiger_read(fileName, verbose);
            kc_gg *ggReverse;

            for (i = 0; i < nAdds;)
            {
                for (j = start; j < gg->size; j++)
                {
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
            while (kc_gg_can_delete_node(gg))
            {
                for (j = start; j < gg->size; j++)
                {
                    iDelete = start + Num % (gg->size - start);
                    iCand = 2 + Num % ((iChange - 2) - 2);
                    ggReverse = gg;
                    kc_gg_delete_node(gg, iDelete, iCand);
                    if (!kc_gg_is_correct(gg))
                        kc_gg_reverse(gg, ggReverse);
                }
            }
        */
        return 1;
    }
}

/*************************************************************
                   main() procedure
**************************************************************/

int main(int argc, char **argv)
{

    char *input = (char *)"../rec-synthesis/outputs/80.aig";
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

        // printf((argv[argc - 1]), "\n");
        kc_top_level_call(input, 10, 1);
    }
}

/*************************************************************
                     End of file
**************************************************************/
