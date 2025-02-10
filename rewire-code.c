/*************************************************************
                       AIG rewiring
**************************************************************/

#define PRINT_DEBUG 0  // set this to 1 to see additional debug printout

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "miniaig.h"

#ifdef _WIN32
typedef unsigned __int64 word;   // 32-bit windows
#else
typedef long long unsigned word; // other platforms
#endif

#ifdef _WIN32
typedef __int64 iword;   // 32-bit windows
#else
typedef long long iword; // other platforms
#endif

/*************************************************************
                 literal manipulation, etc
**************************************************************/

// swapping two variables
#define RW_SWAP(Type, a, b)  { Type t = a; a = b; b = t; }

// min/max/abs
static inline int  AbsInt( int a        )     { return a < 0 ? -a : a; }
static inline int  MaxInt( int a, int b )     { return a > b ?  a : b; }
static inline int  MinInt( int a, int b )     { return a < b ?  a : b; }
 
 // operations on variables and literals
static inline int  Var2Lit( int Var, int c )  { assert(Var >= 0 && !(c >> 1)); return Var + Var + c; }
static inline int  Lit2Var( int Lit )         { assert(Lit >= 0); return Lit >> 1;                   }
static inline int  Lit2C  ( int Lit )         { assert(Lit >= 0); return Lit & 1;                    }
static inline int  LitNot ( int Lit )         { assert(Lit >= 0); return Lit ^ 1;                    }
static inline int  LitNotC( int Lit, int c )  { assert(Lit >= 0); return Lit ^ (int)(c > 0);         }
static inline int  LitReg ( int Lit )         { assert(Lit >= 0); return Lit & ~01;                  }

static inline int  Lit2LitV( int * pMapV2V, int Lit )  { assert(Lit >= 0); return Var2Lit( pMapV2V[Lit2Var(Lit)], Lit2C(Lit) );   }
static inline int  Lit2LitL( int * pMapV2L, int Lit )  { assert(Lit >= 0); return LitNotC( pMapV2L[Lit2Var(Lit)], Lit2C(Lit) );   }

/*************************************************************
                 random number generation
**************************************************************/

// Creates a sequence of random numbers.
// http://www.codeproject.com/KB/recipes/SimpleRNG.aspx

#define NUMBER1  3716960521u
#define NUMBER2  2174103536u

unsigned Random_Int( int fReset )
{
  static unsigned int m_z = NUMBER1;
  static unsigned int m_w = NUMBER2;
  if ( fReset ) {
    m_z = NUMBER1;
    m_w = NUMBER2;
  }
  m_z = 36969 * (m_z & 65535) + (m_z >> 16);
  m_w = 18000 * (m_w & 65535) + (m_w >> 16);
  return (m_z << 16) + m_w;
}
word Random_Word( int fReset )
{
  return ((word)Random_Int(fReset) << 32) | ((word)Random_Int(fReset) << 0);
}

// This procedure should be called once with Seed > 0 to initialize the generator.
// After initialization, the generator should be always called with Seed == 0.
unsigned Random_Num( int Seed )
{
  static unsigned RandMask = 0;
  if ( Seed == 0 )
    return RandMask ^ Random_Int(0);
  RandMask = Random_Int(1);
  for ( int i = 0; i < Seed; i++ )
    RandMask = Random_Int(0);
  return RandMask;
}

/*************************************************************
                 counting wall time
**************************************************************/

static inline iword Time_Clock()
{
#if defined(__APPLE__) && defined(__MACH__)
  #define APPLE_MACH (__APPLE__ & __MACH__)
#else
  #define APPLE_MACH 0
#endif
#if (defined(LIN) || defined(LIN64)) && !APPLE_MACH && !defined(__MINGW32__)
  struct timespec ts;
  if ( clock_gettime(CLOCK_MONOTONIC, &ts) < 0 ) 
      return (iword)-1;
  iword res = ((iword) ts.tv_sec) * CLOCKS_PER_SEC;
  res += (((iword) ts.tv_nsec) * CLOCKS_PER_SEC) / 1000000000;
  return res;
#else
  return (iword) clock();
#endif
}
static inline void Time_Print( const char * pStr, iword time )
{
  printf( "%s = %9.2f sec", pStr, (float)1.0*((double)(time))/((double)CLOCKS_PER_SEC) );
}

/*************************************************************
                 vector of 32-bit integers
**************************************************************/

typedef struct vi_ {
  int    size;
  int    cap;
  int*   ptr;
} vi;

// iterator through the entries in the vector
#define Vi_ForEachEntry(v, entry, i)                for (i = 0; (i < (v)->size) && (((entry) = Vi_Read((v), i)), 1); i++)
#define Vi_ForEachEntryReverse(v, entry, i)         for (i = (v)->size-1; (i >= 0) && (((entry) = Vi_Read((v), i)), 1); i--)
#define Vi_ForEachEntryStart(v, entry, i, start)    for (i = start; (i < (v)->size) && (((entry) = Vi_Read((v), i)), 1); i++)    
#define Vi_ForEachEntryStop(v, entry, i, stop)      for (i = 0; (i < stop) && (((entry) = Vi_Read((v), i)), 1); i++)    

static inline void  Vi_Start  (vi* v, int cap)      { v->size = 0; v->cap = cap; v->ptr = (int*)malloc(sizeof(int)*cap); }
static inline vi*   Vi_Alloc  (int cap)             { vi* v = (vi*)malloc(sizeof(vi)); Vi_Start(v, cap); return v; }
static inline void  Vi_Stop   (vi* v)               { if ( v->ptr ) free(v->ptr);                    }
static inline void  Vi_Free   (vi* v)               { if ( v->ptr ) free(v->ptr); free(v);           }
static inline int   Vi_Size   (vi* v)               { return v->size;                                }
static inline int   Vi_Space  (vi* v)               { return v->cap - v->size;                       }
static inline int*  Vi_Array  (vi* v)               { return v->ptr;                                 }
static inline int   Vi_Read   (vi* v, int k)        { assert(k < v->size); return v->ptr[k];         }
static inline void  Vi_Write  (vi* v, int k, int e) { assert(k < v->size); v->ptr[k] = e;            }
static inline void  Vi_Shrink (vi* v, int k)        { assert(k <= v->size); v->size = k;             } // only safe to shrink !!
static inline int   Vi_Pop    (vi* v)               { assert(v->size > 0); return v->ptr[--v->size]; }
static inline void  Vi_Grow   (vi* v)               {
  if (v->size < v->cap)
    return;
  int newcap = (v->cap < 4) ? 8 : (v->cap / 2) * 3;
  v->ptr = (int*)realloc( v->ptr, sizeof(int)*newcap );
  if ( v->ptr == NULL ) {
    printf( "Failed to realloc memory from %.1f MB to %.1f MB.\n", 4.0 * v->cap / (1<<20), (float)4.0 * newcap / (1<<20) );
    fflush( stdout );
  }
  v->cap = newcap; 
}
static inline vi*   Vi_Dup    (vi* v)               {
  vi* pNew = Vi_Alloc(v->size);
  memcpy( pNew->ptr, v->ptr, sizeof(int)*v->size );
  pNew->size = v->size;
  return pNew;
}
static inline void Vi_Push     (vi* v, int e)            { Vi_Grow(v);  v->ptr[v->size++] = e;              }
static inline void Vi_PushTwo  (vi* v, int e1, int e2)   { Vi_Push(v, e1); Vi_Push(v, e2);                  }
static inline void Vi_PushArray(vi* v, int * p, int n)   { int i; for (i = 0; i < n; i++) Vi_Push(v, p[i]); }
static inline void Vi_PushOrder(vi* v, int e)            { Vi_Push(v, e); if (v->size > 1) for (int i = v->size-2; i >= 0; i--) if (v->ptr[i] > v->ptr[i+1]) RW_SWAP(int, v->ptr[i], v->ptr[i+1]) else break; }
static inline void Vi_Fill     (vi* v, int n, int fill)  { int i; Vi_Shrink(v, 0); for (i = 0; i < n; i++) Vi_Push(v, fill); }
static inline int  Vi_Drop     (vi* v, int i) {
  assert( i >= 0 && i < v->size );
  int Entry = v->ptr[i];
  for ( ; i < v->size-1; i++ ) 
    v->ptr[i] = v->ptr[i+1];
  Vi_Shrink( v, v->size-1 );
  return Entry;
}
static inline int  Vi_Find(vi* v, int e) {
  int j;
  for ( j = 0; j < v->size; j++ )
    if ( v->ptr[j] == e )
      return j;
  return -1;
}
static inline int  Vi_Remove(vi* v, int e) {
  int j = Vi_Find(v, e);
  if ( j == -1 )
    return 0;
  Vi_Drop( v, j );
  return 1;
}
static inline void Vi_Randomize(vi * v) {
  for ( int i = 0; i < v->size; i++ ) {
    int iRand = Random_Num(0) % v->size;
    RW_SWAP( int, v->ptr[iRand], v->ptr[i] );
  }
}
static inline void  Vi_Print(vi* v) {
  printf( "Array with %d entries:", v->size ); int i, entry;
  Vi_ForEachEntry( v, entry, i )
    printf( " %d", entry );
  printf( "\n" );
}
static inline void Vi_SelectSort(vi* v) {
  int * pArray = Vi_Array(v);
  int nSize = Vi_Size(v);
  int temp, i, j, best_i;
  for ( i = 0; i < nSize-1; i++ )
  {
      best_i = i;
      for ( j = i+1; j < nSize; j++ )
          if ( pArray[j] < pArray[best_i] )
              best_i = j;
      temp = pArray[i]; 
      pArray[i] = pArray[best_i]; 
      pArray[best_i] = temp;
  }
}

/*************************************************************
                 truth table manipulation
**************************************************************/

#ifdef LIN // 32-bit Linux
  #define ABC_CONST(number) number ## ULL 
#else // LIN64 and windows
  #define ABC_CONST(number) number
#endif

// the bit count for the first 256 integer numbers
static int Tt_BitCount8[256] = {
    0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
};
static inline int Tt_BitCount16( int i ) { return Tt_BitCount8[i & 0xFF] + Tt_BitCount8[i >> 8]; }

static word s_Truths6[6] = {
  ABC_CONST(0xAAAAAAAAAAAAAAAA),
  ABC_CONST(0xCCCCCCCCCCCCCCCC),
  ABC_CONST(0xF0F0F0F0F0F0F0F0),
  ABC_CONST(0xFF00FF00FF00FF00),
  ABC_CONST(0xFFFF0000FFFF0000),
  ABC_CONST(0xFFFFFFFF00000000)
};
static inline int Tt_HexDigitNum( int n ) { 
  return n <= 2 ? 1 : 1 << (n-2);                      
}
static inline void Tt_Print( word * p, int nWords ) {
    int k, Digit, nDigits = nWords * 16;
    for (k = nDigits - 1; k >= 0; k--)
    {
        Digit = (int)((p[k / 16] >> ((k % 16) * 4)) & 15);
        if (Digit < 10)
            printf("%d", Digit);
        else
            printf("%c", 'A' + Digit - 10);
    }
    printf( "\n" );
}
static inline int Tt_CountOnes( word x ) {
  x = x - ((x >> 1) & ABC_CONST(0x5555555555555555));   
  x = (x & ABC_CONST(0x3333333333333333)) + ((x >> 2) & ABC_CONST(0x3333333333333333));    
  x = (x + (x >> 4)) & ABC_CONST(0x0F0F0F0F0F0F0F0F);    
  x = x + (x >> 8);
  x = x + (x >> 16);
  x = x + (x >> 32); 
  return (int)(x & 0xFF);
}
static inline int Tt_CountOnes2( word x ) {
  return x ? Tt_CountOnes(x) : 0;
}
static inline int Tt_CountOnesVec( word * x, int nWords ) {
  int w, Count = 0;
  for ( w = 0; w < nWords; w++ )
    Count += Tt_CountOnes2( x[w] );
  return Count;
}
static inline int Tt_CountOnesVecMask( word * x, word * pMask, int nWords ) {
  int w, Count = 0;
  for ( w = 0; w < nWords; w++ )
    Count += Tt_CountOnes2( pMask[w] & x[w] );
  return Count;
}
static inline void Tt_Clear( word * pOut, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] = 0;
}
static inline void Tt_Fill( word * pOut, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] = ~(word)0;
}
static inline void Tt_Dup( word * pOut, word * pIn, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] = pIn[w];
}
static inline void Tt_DupC( word * pOut, word * pIn, int fC, int nWords ) {
  int w;
  if ( fC )
    for ( w = 0; w < nWords; w++ )
      pOut[w] = ~pIn[w];
  else
    for ( w = 0; w < nWords; w++ )
      pOut[w] = pIn[w];
}
static inline void Tt_Not( word * pOut, word * pIn, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] = ~pIn[w];
}
static inline void Tt_And( word * pOut, word * pIn1, word * pIn2, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] = pIn1[w] & pIn2[w];
}
static inline void Tt_Sharp( word * pOut, word * pIn, int fC, int nWords ) {
  int w;
  if ( fC )
    for ( w = 0; w < nWords; w++ )
      pOut[w] &= ~pIn[w];
  else
    for ( w = 0; w < nWords; w++ )
      pOut[w] &= pIn[w];
}
static inline void Tt_OrXor( word * pOut, word * pIn1, word * pIn2, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    pOut[w] |= pIn1[w] ^ pIn2[w];
}
static inline int Tt_WordNum( int n ) {
  return n > 6 ? (1 << (n-6)) : 1;
}
static inline void Tt_ElemInit( word * pTruth, int iVar, int nWords ) {
  int k;
  if ( iVar < 6 )
    for ( k = 0; k < nWords; k++ )
      pTruth[k] = s_Truths6[iVar];
  else
    for ( k = 0; k < nWords; k++ )
      pTruth[k] = (k & (1 << (iVar-6))) ? ~(word)0 : 0;
}
static inline int Tt_IntersectC( word * pIn1, word * pIn2, int fC, int nWords ) {
  int w;
  if ( fC ) {
    for ( w = 0; w < nWords; w++ )
      if ( pIn1[w] & ~pIn2[w] )
        return 1;
  }
  else {
    for ( w = 0; w < nWords; w++ )
      if ( pIn1[w] & pIn2[w] )
        return 1;
  }
  return 0;
}
static inline int Tt_Equal( word * pIn1, word * pIn2, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    if ( pIn1[w] != pIn2[w] )
      return 0;
  return 1;
}
static inline int Tt_EqualOnCare( word * pCare, word * pIn1, word * pIn2, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    if ( pCare[w] & (pIn1[w] ^ pIn2[w]) )
      return 0;
  return 1;
}
static inline int Tt_IsConst0( word * pIn, int nWords ) {
  int w;
  for ( w = 0; w < nWords; w++ )
    if ( pIn[w] )
      return 0;
  return 1;
}
// read/write/flip i-th bit of a bit string table:
static inline int     Tt_GetBit( word * p, int k )             { return (int)(p[k>>6] >> (k & 63)) & 1;              }
static inline void    Tt_SetBit( word * p, int k )             { p[k>>6] |= (((word)1)<<(k & 63));                   }
static inline void    Tt_XorBit( word * p, int k )             { p[k>>6] ^= (((word)1)<<(k & 63));                   }


/*************************************************************
                   multi-input node AIG
**************************************************************/

typedef struct maig_ {
  int     nIns;         // primary inputs
  int     nOuts;        // primary outputs
  int     nObjs;        // all objects
  int     nObjsAlloc;   // allocated space
  int     nWords;       // the truth table size
  int     nTravIds;     // traversal ID counter
  int *   pTravIds;     // traversal IDs
  int *   pCopy;        // temp copy
  int *   pRefs;        // reference counters
  word *  pTruths[3];   // truth tables
  word *  pCare;        // careset
  word *  pProd;        // product
  vi *    vOrder;       // node order
  vi *    vOrderF;      // fanin order
  vi *    vOrderF2;     // fanin order
  vi *    vTfo;         // transitive fanout cone
  vi *    pvFans;       // the array of objects' fanins
  int *   pTable;       // structural hashing table
  int     TableSize;    // the size of the hash table
} maig;

#define Maig_ForEachConstInput( p, i )           for (i = 0; i <= p->nIns; i++)
#define Maig_ForEachInput( p, i )                for (i = 1; i <= p->nIns; i++)
#define Maig_ForEachNode( p, i )                 for (i = 1 + p->nIns;         i < p->nObjs - p->nOuts; i++)
#define Maig_ForEachNodeReverse( p, i )          for (i = p->nObjs-p->nOuts-1; i > 1 + p->nIns; i--)
#define Maig_ForEachInputNode( p, i )            for (i = 1;                   i < p->nObjs - p->nOuts; i++)
#define Maig_ForEachNodeStart( p, i, s )         for (i = s;                   i < p->nObjs - p->nOuts; i++)
#define Maig_ForEachOutput( p, i )               for (i = p->nObjs - p->nOuts; i < p->nObjs; i++)
#define Maig_ForEachNodeOutput( p, i )           for (i = 1 + p->nIns;         i < p->nObjs; i++)
#define Maig_ForEachNodeOutputStart( p, i, s )   for (i = s;                   i < p->nObjs; i++)
#define Maig_ForEachObj( p, i )                  for (i = 0;                   i < p->nObjs; i++)
#define Maig_ForEachObjFanin( p, i, iLit, k )    Vi_ForEachEntry( &p->pvFans[i], iLit, k )

static inline int Maig_ObjIsPi( maig * p, int i )   { return i > 0 && i <= p->nIns;                  }
static inline int Maig_ObjIsPo( maig * p, int i )   { return i >= p->nObjs - p->nOuts;               }
static inline int Maig_ObjIsNode( maig * p, int i ) { return i > p->nIns && i < p->nObjs - p->nOuts; }

static inline maig * Maig_Alloc( int nIns, int nOuts, int nObjsAlloc )
{
  assert( 1 + nIns + nOuts <= nObjsAlloc );
  maig * p      = (maig *)calloc( sizeof(maig), 1 ); int i;
  p->nIns       = nIns;
  p->nOuts      = nOuts;
  p->nObjs      = 1 + nIns; // const0 + nIns
  p->nObjsAlloc = nObjsAlloc;  
  p->nWords     = Tt_WordNum(nIns);
  p->nTravIds   = 0;
  p->pTravIds   = (int *)calloc( sizeof(int), p->nObjsAlloc );
  p->pCopy      = (int *)calloc( sizeof(int), p->nObjsAlloc );
  p->pRefs      = (int *)calloc( sizeof(int), p->nObjsAlloc );
  p->vOrder     = Vi_Alloc( 1000 );  
  p->vOrderF    = Vi_Alloc( 1000 );  
  p->vOrderF2   = Vi_Alloc( 1000 );  
  p->vTfo       = Vi_Alloc( 1000 );  
  p->pvFans     = (vi *)calloc( sizeof(vi), p->nObjsAlloc );
  return p;
}
static inline void Maig_Free( maig * p )
{
  int i;
  for ( i = 0; i < p->nObjsAlloc; i++ )
    if ( p->pvFans[i].ptr ) 
      free(p->pvFans[i].ptr);
  free(p->pvFans);
  Vi_Free(p->vOrder);
  Vi_Free(p->vOrderF);
  Vi_Free(p->vOrderF2);
  Vi_Free(p->vTfo);
  free(p->pTravIds);
  free(p->pCopy);
  free(p->pRefs);
  for ( i = 0; i < 3; i++ )
    if ( p->pTruths[i] )
      free(p->pTruths[i]);
  if ( p->pCare )  free(p->pCare);
  if ( p->pProd )  free(p->pProd);    
  if ( p->pTable ) free(p->pTable);
  free(p);
}
static inline void Maig_Print( maig * p )
{
  int i, k, iLit;
  printf( "\nAIG printout:\n" );
  printf( "Const0\n" );
  Maig_ForEachInput( p, i )
    printf( "Pi%d\n", i );
  Maig_ForEachNode( p, i ) {
    printf( "Node%d {", i );
    Maig_ForEachObjFanin( p, i, iLit, k )
      printf( " %d", iLit );
    printf( " }\n" );
  }
  Maig_ForEachOutput( p, i ) {
    printf( "Po%d ", i );
    Maig_ForEachObjFanin( p, i, iLit, k )
      printf( " %d", iLit );
    printf( "\n" );
  }
}

static inline int Maig_AppendObj(maig *p) 
{ 
    assert(p->nObjs < p->nObjsAlloc);
    return p->nObjs++;
}
static inline void Maig_AppendFanin(maig *p, int i, int iLit) 
{ 
    Vi_PushOrder(p->pvFans+i, iLit);
}
static inline int Maig_ObjFaninNum( maig * p, int i )
{
  return Vi_Size(p->pvFans+i);
}
static inline int Maig_ObjFanin0( maig * p, int i )
{
  return Vi_Read(p->pvFans+i, 0);
}
static inline int Maig_ObjFanin1( maig * p, int i )
{
  assert( Maig_ObjFaninNum(p, i) == 2 );
  return Vi_Read(p->pvFans+i, 1);
}

static inline int Maig_CountAnd2( maig * g )
{
  int i, Counter = 0;
  Maig_ForEachNode( g, i )
      Counter += Maig_ObjFaninNum(g, i) - 1;
  return Counter;
}

// reference counting
static inline void Maig_ObjRef( maig * p, int iObj )
{
  int k, iLit;
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    p->pRefs[Lit2Var(iLit)]++;
}
static inline void Maig_ObjDeref( maig * p, int iObj )
{
  int k, iLit;
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    p->pRefs[Lit2Var(iLit)]--;
}
static inline void Maig_ObjDeref_rec( maig * p, int iObj, int iLitSkip )
{
  int k, iLit;
  Maig_ForEachObjFanin( p, iObj, iLit, k ) 
    if ( iLit != iLitSkip && --p->pRefs[Lit2Var(iLit)] == 0 && Maig_ObjIsNode(p, Lit2Var(iLit)) ) {
      Maig_ObjDeref_rec(p, Lit2Var(iLit), -1);
      Vi_Fill(p->pvFans+Lit2Var(iLit), 1, 0);
      Maig_ObjRef(p, Lit2Var(iLit));
    }
}
static inline void Maig_InitializeRefs( maig * p )
{
  int i; memset( p->pRefs, 0, sizeof(int)*p->nObjs );
  Maig_ForEachNodeOutput( p, i )
    Maig_ObjRef( p, i );
}
static inline void Maig_VerifyRefs( maig * p )
{
  int i; 
  Maig_ForEachNodeOutput( p, i )
    Maig_ObjDeref( p, i );
  for ( i = 0; i < p->nObjs; i++ )
    if ( p->pRefs[i] ) 
       printf( "Ref count of node %d is incorrect (%d).\n", i, p->pRefs[i] );
  Maig_InitializeRefs( p );
}


/*************************************************************
                  MiniAIG <--> Maig 
**************************************************************/

static inline maig * Maig_FromMiniAig( Mini_Aig_t * p )
{
  int * pCopy = (int *)calloc( sizeof(int), Mini_AigNodeNum(p) ); // obj2obj
  maig * pNew = Maig_Alloc( Mini_AigPiNum(p), Mini_AigPoNum(p), Mini_AigNodeNum(p) ); int i;
  Maig_ForEachInput( pNew, i )
    pCopy[i] = i;  
  Mini_AigForEachAnd( p, i ) {
    pCopy[i] = Maig_AppendObj(pNew);
    assert( pCopy[i] == i );
    Maig_AppendFanin( pNew, pCopy[i], Lit2LitV(pCopy, Mini_AigNodeFanin0(p, i)) );
    Maig_AppendFanin( pNew, pCopy[i], Lit2LitV(pCopy, Mini_AigNodeFanin1(p, i)) );
  }
  Mini_AigForEachPo( p, i )
    Maig_AppendFanin( pNew, Maig_AppendObj(pNew), Lit2LitV(pCopy, Mini_AigNodeFanin0(p, i)) );
  free( pCopy );
  return pNew;
}
static inline Mini_Aig_t * Maig_ToMiniAig( maig * p )
{
  int i, k, iLit, iLit2, And2 = Maig_CountAnd2(p);
  Mini_Aig_t * pMini = Mini_AigStart();
  memset( p->pCopy, 0, sizeof(int)*p->nObjs );
  Maig_ForEachInput( p, i )
    p->pCopy[i] = Mini_AigCreatePi(pMini);
  Maig_ForEachNode( p, i ) {
    assert( Maig_ObjFaninNum(p, i) > 0 );
    Maig_ForEachObjFanin( p, i, iLit, k )
      if ( k == 0 )
        p->pCopy[i] = Lit2LitL(p->pCopy, iLit);
      else
        p->pCopy[i] = Mini_AigAnd( pMini, p->pCopy[i], Lit2LitL(p->pCopy, iLit) );
  }
  Maig_ForEachOutput( p, i ) {
    int nOuts = Maig_ObjFaninNum(p, i);
    assert( Maig_ObjFaninNum(p, i) == 1 );
    Maig_ForEachObjFanin( p, i, iLit, k )
      Mini_AigCreatePo( pMini, Lit2LitL(p->pCopy, iLit) );
  }
  assert( pMini->nSize == 2 * (1 + p->nIns + p->nOuts + And2) );
  return pMini;    
}

void Rw_DumpAiger( maig * g, char * pFileName )
{
  Mini_Aig_t * p = Maig_ToMiniAig( g );
  Mini_AigerWrite( pFileName, p, 1 );
  Mini_AigStop( p );
}

/*************************************************************
                 MAIG duplicators
**************************************************************/

// this procedure marks Const0, PIs, POs, and used nodes with the current trav ID
static inline void Maig_MarkDfs_rec( maig * p, int iObj )
{
  int i, iLit;
  if ( p->pTravIds[iObj] == p->nTravIds )
    return;
  p->pTravIds[iObj] = p->nTravIds;
  Maig_ForEachObjFanin( p, iObj, iLit, i )
    Maig_MarkDfs_rec(p, Lit2Var(iLit));
}
static inline int Maig_MarkDfs( maig * p )
{
  int i, nUnused = 0;
  p->nTravIds++;
  Maig_ForEachConstInput( p, i )
    p->pTravIds[i] = p->nTravIds;
  Maig_ForEachOutput( p, i )
    Maig_MarkDfs_rec( p, Lit2Var(Maig_ObjFanin0(p, i)) );
  Maig_ForEachOutput( p, i )
    p->pTravIds[i] = p->nTravIds;   
  Maig_ForEachNode( p, i )
    nUnused += (int)(p->pTravIds[i] != p->nTravIds);
  return nUnused;
}

// simple duplicator (optionally removes unused nodes)
static inline maig * Maig_Dup( maig * p, int fRemDangle )
{
  maig * pNew = Maig_Alloc( p->nIns, p->nOuts, p->nObjs );
  memset( p->pCopy, 0, sizeof(int)*p->nObjs ); int i, k, iLit; // obj2obj
  if ( fRemDangle )  
    Maig_MarkDfs(p);
  Maig_ForEachInput( p, i )
    p->pCopy[i] = i;
  Maig_ForEachNodeOutput( p, i ) {
    assert( Maig_ObjFaninNum(p, i) > 0 );
    if ( fRemDangle && p->pTravIds[i] != p->nTravIds )
      continue;
    p->pCopy[i] = Maig_AppendObj(pNew);
    Maig_ForEachObjFanin( p, i, iLit, k )
      Maig_AppendFanin(pNew, p->pCopy[i], Lit2LitV(p->pCopy, iLit));
  }
  return pNew;
}

// duplicator to restore the topological order 
// (the input AIG can have "hidden" internal nodes listed after primary outputs)
static inline void Maig_DupDfs_rec( maig * pNew, maig * p, int iObj )
{
  int i, iLit; 
  // 1. return if current node is already marked
  if ( p->pCopy[iObj] >= 0 ) 
    return;
  // 2. create fanins for a given node
  Maig_ForEachObjFanin( p, iObj, iLit, i )
    Maig_DupDfs_rec( pNew, p, Lit2Var(iLit) );
  assert( p->pCopy[iObj] < 0 ); // combinational loop catching
  assert( Maig_ObjFaninNum(p, iObj) > 0 );
  // 3. create current node
  p->pCopy[iObj] = Maig_AppendObj(pNew);
  // 4. append newly created fanins to the current node    
  Maig_ForEachObjFanin( p, iObj, iLit, i )
    Maig_AppendFanin(pNew, p->pCopy[iObj], Lit2LitV(p->pCopy, iLit));
}
static inline maig * Maig_DupDfs( maig * p )
{
  maig * pNew = Maig_Alloc( p->nIns, p->nOuts, p->nObjsAlloc );
  // 1. the array is filled with -1 to distinct visited nodes from unvisited
  memset( p->pCopy, 0xFF, sizeof(int)*p->nObjsAlloc ); int i, k, iLit; // obj2obj
  // for each primary input we mark it with it's index
  Maig_ForEachConstInput( p, i )
    p->pCopy[i] = i;
  // 2. for each primary output we call recursive function for it's fanin  
  Maig_ForEachOutput( p, i )
    Maig_DupDfs_rec( pNew, p, Lit2Var(Maig_ObjFanin0(p, i)) );
  // 3. for each primary output append it's fanin
  Maig_ForEachOutput( p, i )
    Maig_AppendFanin(pNew, Maig_AppendObj(pNew), Lit2LitV(p->pCopy, Maig_ObjFanin0(p, i)));
  return pNew;
}

// reduces multi-input and-gate represented by an array of fanin literals
static inline void Maig_ReduceFanins(vi* v) 
{
  assert( Vi_Size(v) > 0 );
  Vi_SelectSort(v);
  if ( Vi_Read(v, 0) == 0 ) {
    Vi_Shrink(v, 1);
    return;
  }
  while ( Vi_Read(v, 0) == 1 )
    Vi_Drop(v, 0);
  if ( Vi_Size(v) == 0 ) {
    Vi_Push(v, 1 );
    return;
  }
  if ( Vi_Size(v) == 1 )
    return;
  int i, iLit, iPrev = Vi_Read(v, 0);
  Vi_ForEachEntryStart( v, iLit, i, 1 ) {
    if ( (iPrev ^ iLit) == 1 ) {
      Vi_Fill(v, 1, 0);
      return;      
    }
    if ( iPrev == iLit )
      Vi_Drop(v, i--);
    else
      iPrev = iLit;
  }
}

// naive structural hashing
static inline int Maig_StrashNode2( maig * p, int l0, int l1 ) 
{
  int lit0 = MinInt(l0, l1);
  int lit1 = MaxInt(l0, l1), i;  
  Maig_ForEachNode( p, i )
    if ( Maig_ObjFanin0(p, i) == lit0 && Maig_ObjFanin1(p, i) == lit1 )
      return Var2Lit(i, 0);
  return -1;
}
static inline int Maig_BuildNode2( maig * p, int l0, int l1, int fCprop, int fStrash ) 
{
  if ( fCprop ) {
    if ( l0 == 0  || l1 == 0 || (l0 ^ l1) == 1 ) return 0;
    if ( l0 == l1 || l1 == 1 )                   return l0;
    if ( l0 == 1 )                               return l1;
  }
  if ( fStrash ) {
    int Lit = Maig_StrashNode2( p, l0, l1 );
    if ( Lit != -1 )
      return Lit;
  }
  int iObj = Maig_AppendObj(p);
  Maig_AppendFanin( p, iObj, MinInt(l0, l1) );
  Maig_AppendFanin( p, iObj, MaxInt(l0, l1) );
  return Var2Lit(iObj, 0);
}

// smart structural hashing
static inline int Maig_HashTwo( int l0, int l1, int TableSize ) 
{
    unsigned Key = 0;
    Key += Lit2Var(l0) * 7937;
    Key += Lit2Var(l1) * 2971;
    Key += Lit2C(l0) * 911;
    Key += Lit2C(l1) * 353;
    return Key % TableSize;
}
static inline int * Maig_HashLookup( int * pTable, int l0, int l1, int TableSize ) 
{
  int Key = Maig_HashTwo(l0, l1, TableSize);
  for ( ; pTable[3*Key]; Key = (Key + 1) % TableSize )
    if ( pTable[3*Key] == l0 && pTable[3*Key+1] == l1 )
       return pTable+3*Key+2;
  assert( pTable[3*Key] == 0 );
  assert( pTable[3*Key+1] == 0 );
  assert( pTable[3*Key+2] == 0 );
  pTable[3*Key] = l0;
  pTable[3*Key+1] = l1;
  return pTable+3*Key+2;
}

// this duplicator creates two-input nodes, propagates constants, and does structural hashing
static inline int Maig_BuildNode( maig * p, int l0, int l1, int fCprop, int fStrash ) 
{
  if ( fCprop ) {
    if ( l0 == 0  || l1 == 0 || (l0 ^ l1) == 1 ) return 0;
    if ( l0 == l1 || l1 == 1 )                   return l0;
    if ( l0 == 1 )                               return l1;
  }
  int * pPlace = NULL;
  if ( fStrash ) {
    pPlace = Maig_HashLookup( p->pTable, MinInt(l0, l1), MaxInt(l0, l1), p->TableSize );
    if ( *pPlace )
      return *pPlace;
  }
  int iObj = Maig_AppendObj(p);
  Maig_AppendFanin( p, iObj, MinInt(l0, l1) );
  Maig_AppendFanin( p, iObj, MaxInt(l0, l1) );
  return pPlace ? (*pPlace = Var2Lit(iObj, 0)) : Var2Lit(iObj, 0);
}
// Returns the next prime >= p
static inline int Abc_PrimeCudd( unsigned int p )
{
    int i,pn;
    p--;
    do {
        p++;
        if (p&1)
        {
            pn = 1;
            i = 3;
            while ((unsigned) (i * i) <= p)
            {
                if (p % (unsigned)i == 0) {
                    pn = 0;
                    break;
                }
                i += 2;
            }
        }
        else
            pn = 0;
    } while (!pn);
    return (int)(p);

} // end of Cudd_Prime 
static inline maig * Maig_DupStrash( maig * p, int fCprop, int fStrash )
{
  int i, k, iLit, nObjsAlloc = 1 + p->nIns + p->nOuts + Maig_CountAnd2(p);
  maig * pTemp, * pNew = Maig_Alloc( p->nIns, p->nOuts, nObjsAlloc );
  memset( p->pCopy, 0, sizeof(int)*p->nObjs ); // obj2lit
  if ( fStrash ) {
    assert( pNew->pTable == NULL );
    pNew->TableSize = Abc_PrimeCudd( 3 * Maig_CountAnd2(p) ); 
    pNew->pTable = (int *)calloc(sizeof(int), 3*pNew->TableSize);
  }
  Maig_ForEachInput( p, i )
    p->pCopy[i] = Var2Lit(i, 0);
  Maig_ForEachNode( p, i ) {
    assert( Maig_ObjFaninNum(p, i) > 0 );
    Maig_ForEachObjFanin( p, i, iLit, k )
      if ( k == 0 )
        p->pCopy[i] = Lit2LitL(p->pCopy, iLit);
      else 
//        p->pCopy[i] = Maig_BuildNode2(pNew, p->pCopy[i], Lit2LitL(p->pCopy, iLit), fCprop, fStrash);
        p->pCopy[i] = Maig_BuildNode(pNew, p->pCopy[i], Lit2LitL(p->pCopy, iLit), fCprop, fStrash);
  }
  Maig_ForEachOutput( p, i )
    Maig_AppendFanin(pNew, Maig_AppendObj(pNew), Lit2LitL(p->pCopy, Maig_ObjFanin0(p, i)));
  pNew = Maig_Dup( pTemp = pNew, 1 );
  Maig_Free( pTemp );
  return pNew;  
}

// this duplicator converts two-input-node AIG into multi-input-node AIG
static inline int * Maig_CreateStops( maig * p )
{
  int i, * pStop = (int *)calloc( sizeof(int), p->nObjs );
  Maig_ForEachConstInput( p, i )
    pStop[i] = 2;
  Maig_ForEachNode( p, i ) {
    assert( Maig_ObjFaninNum(p, i) == 2 );
    int iLit0 = Maig_ObjFanin0(p, i);
    int iLit1 = Maig_ObjFanin1(p, i);
    pStop[Lit2Var(iLit0)] += 1 + Lit2C(iLit0);
    pStop[Lit2Var(iLit1)] += 1 + Lit2C(iLit1);
  }
  Maig_ForEachOutput( p, i )
    pStop[Lit2Var(Maig_ObjFanin0(p, i))] += 2;
  return pStop;
}
static inline void Maig_CollectSuper_rec( maig * p, int iLit, int * pStop, vi * vSuper )
{
  if ( pStop[Lit2Var(iLit)] > 1 )
    Vi_Push(vSuper, Lit2LitL(p->pCopy, iLit));
  else {
    assert( Lit2C(iLit) == 0 );
    Maig_CollectSuper_rec( p, Maig_ObjFanin0(p, Lit2Var(iLit)), pStop, vSuper );
    Maig_CollectSuper_rec( p, Maig_ObjFanin1(p, Lit2Var(iLit)), pStop, vSuper );
  }
}
static inline maig * Maig_DupMulti( maig * p, int nFaninMax_, int nGrowth )
{
  maig * pNew = Maig_Alloc( p->nIns, p->nOuts, p->nObjs );
  int * pStop = Maig_CreateStops(p); int i, k, iLit;
  vi * vArray = Vi_Alloc( 100 );
  assert( nFaninMax_ >= 2 && nGrowth >= 1 );
  memset( p->pCopy, 0, sizeof(int)*p->nObjs ); // obj2lit
  Maig_ForEachConstInput( p, i )
    p->pCopy[i] = Var2Lit(i, 0);  
  Maig_ForEachNode( p, i ) {
    if ( pStop[i] == 1 )
       continue;
    assert( pStop[i] > 1 ); // no dangling
    Vi_Shrink(vArray, 0);
    Maig_CollectSuper_rec( p, Maig_ObjFanin0(p, i), pStop, vArray );
    Maig_CollectSuper_rec( p, Maig_ObjFanin1(p, i), pStop, vArray );
    assert( Vi_Size(vArray) > 1 );
    Maig_ReduceFanins(vArray);
    assert( Vi_Size(vArray) > 0 );
    if ( Vi_Size(vArray) == 1 ) 
      p->pCopy[i] = Vi_Read(vArray, 0);
    else
    {
      int nFaninMaxLocal = 2 + (Random_Num(0) % (nFaninMax_-1));
      int nGrowthLocal   = 1 + (Random_Num(0) % nGrowth);
      assert( nFaninMaxLocal >= 2 && nFaninMaxLocal <= nFaninMax_ );
      assert( nGrowthLocal   >= 1 && nGrowthLocal   <= nGrowth );
      
      if ( Vi_Size(vArray) > nFaninMaxLocal )
        Vi_Randomize(vArray);
      // create a cascade of nodes
      while ( Vi_Size(vArray) > nFaninMaxLocal )
      {
        int iObj = Maig_AppendObj(pNew);
        vi * vFanins = pNew->pvFans + iObj;
        assert( vFanins->ptr == NULL );
        vFanins->cap = nFaninMaxLocal + nGrowthLocal;
        vFanins->ptr = (int*)malloc( sizeof(int)*vFanins->cap );
        Vi_ForEachEntryStop( vArray, iLit, k, nFaninMaxLocal )
          Maig_AppendFanin( pNew, iObj, iLit );
        assert( Vi_Space(vFanins) == nGrowthLocal );
        for ( k = 0; k < nFaninMaxLocal; k++ )
          Vi_Drop(vArray, 0);
        Vi_Push(vArray, Var2Lit(iObj, 0));
      }
      // create the last node
      int iObj = Maig_AppendObj(pNew);
      vi * vFanins = pNew->pvFans + iObj;
      assert( vFanins->ptr == NULL );
      vFanins->cap = Vi_Size(vArray) + nGrowthLocal;
      vFanins->ptr = (int*)malloc( sizeof(int)*vFanins->cap );
      Vi_ForEachEntry( vArray, iLit, k )
        Maig_AppendFanin( pNew, iObj, iLit );
      assert( Vi_Space(vFanins) == nGrowthLocal );
      p->pCopy[i] = Var2Lit(iObj, 0);
    }
  }
  Maig_ForEachOutput( p, i ) 
    Maig_AppendFanin(pNew, Maig_AppendObj(pNew), Lit2LitL(p->pCopy, Maig_ObjFanin0(p, i)));
  Vi_Stop( vArray );
  free( pStop );
  return pNew;
}

/*************************************************************
                 shared logic extraction
**************************************************************/

// adds fanin pair to storage 
static inline void Rw_AddPair( vi * vPair, int iFan1, int iFan2 )
{
  assert( iFan1 < iFan2 );
  int i, * pArray = Vi_Array(vPair);
  assert( Vi_Size(vPair) % 3 == 0 );
  for ( i = 0; i < Vi_Size(vPair); i += 3 )
    if ( pArray[i] == iFan1 && pArray[i+1] == iFan2 )
      break;
  if ( i == Vi_Size(vPair) ) {
    Vi_Push( vPair, iFan1 );
    Vi_Push( vPair, iFan2 );
    Vi_Push( vPair, 1 );
    pArray = Vi_Array(vPair);
  }
  pArray[i+2]++;
  //printf( "Adding pair (%d, %d)\n", iFan1, iFan2 );
}
// find fanin pair that appears most often
static inline int Rw_FindPair( vi * vPair )
{
  int iBest = -1, BestCost = 0;
  int i, * pArray = Vi_Array(vPair);
  assert( Vi_Size(vPair) % 3 == 0 );
  for ( i = 0; i < Vi_Size(vPair); i += 3 )
    if ( BestCost < pArray[i+2] ) {
      BestCost = pArray[i+2];
      iBest = i;
    }
  //if ( iBest >= 0 ) printf( "Extracting pair (%d, %d) used %d times.\n", pArray[iBest], pArray[iBest+1], pArray[iBest+2] );
  return iBest;
}
// updates one fanin array by replacing the pair with a new literal (iLit)
static inline int Rw_UpdateFanins( vi * vFans, int iFan1, int iFan2, int iLit )
{
  int i, f1, f2, iFan1_, iFan2_;
  Vi_ForEachEntry( vFans, iFan1_, f1 )
  if ( iFan1_ == iFan1 )
  Vi_ForEachEntryStart( vFans, iFan2_, f2, f1+1 )
  if ( iFan2_ == iFan2 )
  {
    assert( f1 < f2 );
    Vi_Drop( vFans, f2 );
    Vi_Drop( vFans, f1 );
    Vi_Push( vFans, iLit );
    return 1;
  }
  return 0;
}
// updates the network by extracting one pair
static inline void Rw_ExtractBest( maig * p, vi * vPairs )
{
  int i, iObj = Maig_AppendObj( p );
  int Counter = 0, * pArray = Vi_Array(vPairs);
  int iBest = Rw_FindPair( vPairs );  assert( iBest >= 0 );
  //printf( "Creating node %d with fanins (%d, %d).\n", iObj, pArray[iBest], pArray[iBest+1] ); 
  assert( Vi_Size(p->pvFans+iObj) == 0 );
  Maig_AppendFanin( p, iObj, pArray[iBest] );
  Maig_AppendFanin( p, iObj, pArray[iBest+1] );
  Maig_ForEachNode( p, i )
    Counter += Rw_UpdateFanins( p->pvFans+i, pArray[iBest], pArray[iBest+1], Var2Lit(iObj, 0) );
  assert( Counter == pArray[iBest+2] );
}
// find the set of all pairs that appear more than once
static inline vi * Rw_FindPairs( maig * p, word * pSto, int nWords )
{
  vi * vPairs = Vi_Alloc( 30 );
  int i, f1, f2, iFan1, iFan2;
  Maig_ForEachNode( p, i )
  {
    vi * vFans = p->pvFans+i;
    Vi_ForEachEntry( vFans, iFan1, f1 ) {
      word * pRowFan1 = pSto + iFan1*nWords;
      Vi_ForEachEntryStart( vFans, iFan2, f2, f1+1 )
        if ( Tt_GetBit(pRowFan1, iFan2) )
          Rw_AddPair( vPairs, iFan1, iFan2 );
        else
          Tt_SetBit(pRowFan1, iFan2);
    }
  }
  return vPairs;
}
// extract shared fanin pairs and return the number of pairs extracted
static inline int Rw_FindShared( maig * p, int nNewNodesMax )
{
  if ( p->nObjs + nNewNodesMax > p->nObjsAlloc ) 
  {
    p->nObjsAlloc = p->nObjs + nNewNodesMax;
    p->pCopy      = (int *)realloc( (void *)p->pCopy,  sizeof(int)*p->nObjsAlloc );
    p->pvFans     =  (vi *)realloc( (void *)p->pvFans, sizeof(vi) *p->nObjsAlloc );
    memset( p->pCopy+p->nObjs,  0, sizeof(int)*(p->nObjsAlloc-p->nObjs) );
    memset( p->pvFans+p->nObjs, 0, sizeof(vi) *(p->nObjsAlloc-p->nObjs) );
  }
  assert( sizeof(word) == 8 );
  int i, nWords = (2*p->nObjsAlloc + 63)/64; // how many words are needed to have a bitstring with one bit for each literal
  int nBytesAll = sizeof(word)*nWords*2*p->nObjsAlloc;
  word * pSto = (word *)malloc(nBytesAll); vi * vPairs;
  for ( i = 0; i < nNewNodesMax; i++ ) {
    memset( pSto, 0, nBytesAll );
    p->nObjs -= i;    
    vPairs = Rw_FindPairs( p, pSto, nWords );
    p->nObjs += i;    
    if ( Vi_Size(vPairs) > 0 )
      Rw_ExtractBest( p, vPairs );
    int Size = Vi_Size(vPairs);
    Vi_Stop( vPairs );
    if ( Size == 0 )
      break;
  }
  free( pSto );
  return i;
}
// perform shared logic extraction
static inline maig * Rw_Share( maig * p, int nNewNodesMax )
{
  maig * pNew, * pCopy = Maig_Dup(p, 0);
  int nNewNodes = Rw_FindShared( pCopy, nNewNodesMax );
  if ( nNewNodes == 0 )
    return pCopy;
  // temporarily create "hidden" nodes for DFS duplicator
  pCopy->nObjs -= nNewNodes;
  pNew = Maig_DupDfs( pCopy );
  pCopy->nObjs += nNewNodes;
  Maig_Free( pCopy );
  return pNew;
}

/*************************************************************
                   care-set computation
**************************************************************/

static inline word * Maig_ObjTruth( maig *p, int i, int n )  { return p->pTruths[n] + p->nWords*i;    }
static inline int    Maig_ObjType( maig *p, int i )          { return p->pTravIds[i] == p->nTravIds;  }

// compute truth table of the node
static inline void Maig_TruthSimNode( maig * p, int i )
{
  int k, iLit;  
  Maig_ForEachObjFanin( p, i, iLit, k )
    if ( k == 0 )
      Tt_DupC( Maig_ObjTruth(p, i, Maig_ObjType(p,i)), Maig_ObjTruth(p, Lit2Var(iLit), Maig_ObjType(p,Lit2Var(iLit))), Lit2C(iLit), p->nWords );
    else
      Tt_Sharp( Maig_ObjTruth(p, i, Maig_ObjType(p,i)), Maig_ObjTruth(p, Lit2Var(iLit), Maig_ObjType(p,Lit2Var(iLit))), Lit2C(iLit), p->nWords );
}
// compute truth table of the node using a subset of its current fanin
static inline word * Maig_TruthSimNodeSubset( maig * p, int i, int m )
{
  int k, iLit, Counter = 0; assert( m > 0 );
  Maig_ForEachObjFanin( p, i, iLit, k )
    if ( (m >> k) & 1 ) { // fanin is included in the subset
      if ( Counter++ == 0 )
        Tt_DupC( p->pProd, Maig_ObjTruth(p, Lit2Var(iLit), 0), Lit2C(iLit), p->nWords );
      else
        Tt_Sharp( p->pProd, Maig_ObjTruth(p, Lit2Var(iLit), 0), Lit2C(iLit), p->nWords );
    }
  assert( Counter == Tt_BitCount16(m) );
  return p->pProd;
}
static inline word * Maig_TruthSimNodeSubset2( maig * p, int i, vi * vFanins, int nFanins )
{
  int k, iLit;
  Vi_ForEachEntryStop( vFanins, iLit, k, nFanins )
    if ( k == 0 )
      Tt_DupC( p->pProd, Maig_ObjTruth(p, Lit2Var(iLit), 0), Lit2C(iLit), p->nWords );
    else
      Tt_Sharp( p->pProd, Maig_ObjTruth(p, Lit2Var(iLit), 0), Lit2C(iLit), p->nWords );
  return p->pProd;
}
static inline void Maig_TruthInitialize( maig * p )
{
  int i, k, iLit;
  if ( p->pTruths[0] ) 
    return;
  p->pTruths[0] = (word *)calloc( sizeof(word), p->nWords*p->nObjs );
  p->pTruths[1] = (word *)calloc( sizeof(word), p->nWords*p->nObjs );
  p->pTruths[2] = (word *)calloc( sizeof(word), p->nWords*p->nObjs );
  p->pCare      = (word *)calloc( sizeof(word), p->nWords );
  p->pProd      = (word *)calloc( sizeof(word), p->nWords );
  float MemMB = 8.0*p->nWords*(3*p->nObjs+2)/(1<<20);
  if ( MemMB > 100.0 )
    printf( "Allocated %d truth tables of %d-variable functions (%.2f MB),\n", 3*p->nObjs+2, p->nIns, MemMB );  
  p->nTravIds++;
  Maig_ForEachInput( p, i )
    Tt_ElemInit( Maig_ObjTruth(p, i, 0), i-1, p->nWords );
  Maig_ForEachNodeOutput( p, i )
    Maig_TruthSimNode( p, i );
  Maig_ForEachOutput( p, i )
    assert( Maig_ObjFaninNum(p, i) == 1 );
  Maig_ForEachOutput( p, i )
    Tt_Dup( Maig_ObjTruth(p, i, 2), Maig_ObjTruth(p, i, 0), p->nWords );
}
static inline void Maig_TruthUpdate( maig * p, vi * vTfo )
{
  int i, iTemp, nFails = 0;
  p->nTravIds++;
  Vi_ForEachEntry( vTfo, iTemp, i ) {
    Maig_TruthSimNode( p, iTemp );
    if ( Maig_ObjIsPo(p, iTemp) && !Tt_Equal(Maig_ObjTruth(p, iTemp, 2), Maig_ObjTruth(p, iTemp, 0), p->nWords) )
      printf( "Verification failed at output %d.\n", iTemp - (p->nObjs - p->nOuts) ), nFails++;
  }
  if ( nFails )
    printf( "Verification failed for %d outputs after updating node %d.\n", nFails, Vi_Read(vTfo,0) );
}
static inline int Maig_ComputeTfo_rec( maig * p, int iObj )
{
  int k, iLit, Value = 0;
  if ( p->pTravIds[iObj] == p->nTravIds )
    return 1;
  if ( p->pTravIds[iObj] == p->nTravIds-1 )
    return 0;
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    Value |= Maig_ComputeTfo_rec(p, Lit2Var(iLit));
  p->pTravIds[iObj] = p->nTravIds-1+Value;
  if ( Value ) Vi_Push( p->vTfo, iObj );
  return Value;
}
static inline vi * Maig_ComputeTfo( maig * p, int iObj )
{
  int i;
  assert( Maig_ObjIsNode(p, iObj) );
  p->nTravIds += 2;
  p->pTravIds[iObj] = p->nTravIds;
  Vi_Fill( p->vTfo, 1, iObj );
  Maig_ForEachConstInput( p, i )
    p->pTravIds[i] = p->nTravIds-1;
  Maig_ForEachOutput( p, i )
    Maig_ComputeTfo_rec( p, i );
  return p->vTfo;
}
static inline word * Maig_ComputeCareSet( maig * p, int iObj )
{
  vi * vTfo = Maig_ComputeTfo( p, iObj );  int i, iTemp;
  Tt_Not( Maig_ObjTruth(p, iObj, 1), Maig_ObjTruth(p, iObj, 0), p->nWords );
  Tt_Clear( p->pCare, p->nWords );
  Vi_ForEachEntryStart( vTfo, iTemp, i, 1 ) {
    Maig_TruthSimNode( p, iTemp );
    if ( Maig_ObjIsPo(p, iTemp) )
      Tt_OrXor( p->pCare, Maig_ObjTruth(p, iTemp, 0), Maig_ObjTruth(p, iTemp, 1), p->nWords );
  }
  return p->pCare;
}

/*************************************************************
                  fanin addition/deletion 
**************************************************************/

static inline int Rw_CheckConst( maig * p, int iObj, word * pCare )
{
  word * pFunc = Maig_ObjTruth(p, iObj, 0);
  if ( !Tt_IntersectC(pCare, pFunc, 0, p->nWords) )
  {
    Maig_ObjDeref_rec( p, iObj, -1 );
    Vi_Fill( p->pvFans+iObj, 1, 0 ); // const0
    Maig_ObjRef( p, iObj );
    Maig_TruthUpdate( p, p->vTfo );
    if ( PRINT_DEBUG ) printf( "Detected Const0 at node %d.\n", iObj );
    return 1;
  }
  if ( !Tt_IntersectC(pCare, pFunc, 1, p->nWords) )
  {
    Maig_ObjDeref_rec( p, iObj, -1 );
    Vi_Fill( p->pvFans+iObj, 1, 1 ); // const1
    Maig_ObjRef( p, iObj );
    Maig_TruthUpdate( p, p->vTfo );
    if ( PRINT_DEBUG ) printf( "Detected Const1 at node %d.\n", iObj );
    return 1;
  }
  return 0;
}
static inline int Rw_ExpandOne( maig * p, int iObj, int nAddedMax )
{
  //printf( "e%d ", iObj ); fflush(stdout);
  int i, k, n, iLit, nFans = Maig_ObjFaninNum(p, iObj), nAdded = 0;
  word * pCare = Maig_ComputeCareSet( p, iObj );
//  if ( Rw_CheckConst(p, iObj, pCare) )
//    return 0;
  assert( nAddedMax > 0 );
  assert( nAddedMax <= Vi_Space(p->pvFans+iObj) );
  // mark node's fanins
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    p->pTravIds[Lit2Var(iLit)] = p->nTravIds;
  // compute the onset
  word * pOnset = Maig_ObjTruth( p, iObj, 0 );
  Tt_Sharp( pOnset, pCare, 0, p->nWords );
  // create a random order of fanin candidates 
  if ( 1 ) {
    Vi_Shrink( p->vOrderF, 0 );
    Maig_ForEachInputNode( p, i )
      if ( p->pTravIds[i] != p->nTravIds && (Maig_ObjIsPi(p, i) || (Maig_ObjFaninNum(p, i) > 1 && p->pRefs[i] > 0)) ) // this node is NOT in the TFO
//      if ( p->pTravIds[i] != p->nTravIds ) // this node is NOT in the TFO
        Vi_Push( p->vOrderF, i );
    Vi_Randomize(p->vOrderF);
  }
  else {
    // put high-fanout references first
    Vi_Shrink( p->vOrderF, 0 );
    Maig_ForEachNode( p, i )
      if ( p->pTravIds[i] != p->nTravIds && p->pRefs[i] > 1 ) // this node is NOT in the TFO
        Vi_Push( p->vOrderF, i );
    Vi_Randomize(p->vOrderF);
    // put primary inputs and low-fanout references second
    Vi_Shrink( p->vOrderF2, 0 );
    Maig_ForEachInput( p, i )
      if ( p->pTravIds[i] != p->nTravIds )
        Vi_Push( p->vOrderF2, i );
    Maig_ForEachNode( p, i )
      if ( p->pTravIds[i] != p->nTravIds && p->pRefs[i] == 1 ) // this node is NOT in the TFO
        Vi_Push( p->vOrderF2, i );
    Vi_Randomize(p->vOrderF2);
    Vi_PushArray(p->vOrderF, Vi_Array(p->vOrderF2), Vi_Size(p->vOrderF2));
  }

  // iterate through candidate fanins (nodes that are not in the TFO of iObj)
  //Maig_ForEachInputNode( p, i ) {
  Vi_ForEachEntry( p->vOrderF, i, k ) {
    assert( p->pTravIds[i] != p->nTravIds );
    // new fanin can be added if its offset does not intersect with the node's onset
    for ( n = 0; n < 2; n++ )
    if ( !Tt_IntersectC(pOnset, Maig_ObjTruth(p, i, 0), !n, p->nWords) ) {
        if ( PRINT_DEBUG ) printf( "Adding node %d fanin %d\n", iObj, Var2Lit(i, n) );
        Maig_AppendFanin(p, iObj, Var2Lit(i, n));
        p->pRefs[i]++;
        nAdded++;
        break;
    }
    if ( nAdded == nAddedMax )
      break;
  }
  //printf( "Updating TFO of node %d:  ", iObj );  Vi_Print(p->vTfo);
  Maig_TruthUpdate( p, p->vTfo );
  //assert( Maig_ObjFaninNum(p, iObj) <= nFaninMax );
  return nAdded;
}


static inline int Rw_ReduceFanins( maig * p, int i, int m )
{
  int nFans = Maig_ObjFaninNum(p, i);
  int k, iLit, Counter = 0; assert( m > 0 );
  int * pFanins = Vi_Array(&p->pvFans[i]);
  Maig_ForEachObjFanin( p, i, iLit, k )
    if ( (m >> k) & 1 )
      pFanins[Counter++] = iLit;
  Vi_Shrink( &p->pvFans[i], Counter );
  assert( Counter == Tt_BitCount16(m) );
  return nFans - Counter;
}
static inline int Rw_ReduceOne( maig * p, int iObj, int fOnlyConst, int fOnlyBuffer )
{
  //printf( "r%d ", iObj ); fflush(stdout);
  int i, n, nFans = Maig_ObjFaninNum(p, iObj), m, nMints = 1 << nFans;
  word * pCare = Maig_ComputeCareSet( p, iObj );
  if ( Rw_CheckConst(p, iObj, pCare) )
    return nFans;
  if ( fOnlyConst )
    return 0;    
  // find a minimum fanin subset whose function is equal to the function of the node on the care set
  word * pFunc = Maig_ObjTruth( p, iObj, 0 ), * pProd;  
  for ( n = 1; n < nFans; n++ )
  for ( m = 1; m < nMints-1; m++ )
    if ( Tt_BitCount16(m) == n ) {
      pProd = Maig_TruthSimNodeSubset( p, iObj, m );
      if ( Tt_EqualOnCare(pCare, pFunc, pProd, p->nWords) ) {
        Maig_ObjDeref( p, iObj );
        int Value = Rw_ReduceFanins(p, iObj, m);;
        Maig_ObjRef( p, iObj );
        Maig_TruthUpdate( p, p->vTfo );
        if ( PRINT_DEBUG ) printf( "Reducing node %d fanin count from %d to %d.\n", iObj, nFans, Maig_ObjFaninNum(p, iObj) );
        return Value;
      }
    }
  pProd = Maig_TruthSimNodeSubset( p, iObj, nMints-1 );
  assert( Tt_EqualOnCare(pCare, pFunc, pProd, p->nWords) );
  return 0;
}

// this procedure tries to prioritize fanins during reduction
static inline int Rw_ReduceOne2( maig * p, int iObj, int fOnlyConst, int fOnlyBuffer )
{
  //printf( "r%d ", iObj ); fflush(stdout);
  int i, n, k, iLit, nFans = Maig_ObjFaninNum(p, iObj);
  word * pCare = Maig_ComputeCareSet( p, iObj );
  if ( Rw_CheckConst(p, iObj, pCare) )
    return nFans;
  if ( fOnlyConst )
    return 0;
  if ( nFans == 1 )
    return 0;
  // if one fanin can be used, take it
  word * pFunc = Maig_ObjTruth( p, iObj, 0 );
  Maig_ForEachObjFanin( p, iObj, iLit, k ) { 
    Tt_DupC( p->pProd, Maig_ObjTruth(p, Lit2Var(iLit), 0), Lit2C(iLit), p->nWords );
    if ( Tt_EqualOnCare(pCare, pFunc, p->pProd, p->nWords) ) {
      Maig_ObjDeref( p, iObj );
      Vi_Fill( p->pvFans+iObj, 1, iLit );
      Maig_ObjRef( p, iObj );
      Maig_TruthUpdate( p, p->vTfo );
      if ( PRINT_DEBUG ) printf( "Reducing node %d fanin count from %d to %d.\n", iObj, nFans, Maig_ObjFaninNum(p, iObj) );
      return nFans-1;      
    }
  }
  if ( fOnlyBuffer )
    return 0;
  // create order of fanins with high reference fanins first
  Vi_Shrink( p->vOrderF, 0 );
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    if ( p->pRefs[Lit2Var(iLit)] > 2 )
      Vi_Push( p->vOrderF, iLit );
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    if ( p->pRefs[Lit2Var(iLit)] == 2 )
      Vi_Push( p->vOrderF, iLit );
  Maig_ForEachObjFanin( p, iObj, iLit, k )
    if ( p->pRefs[Lit2Var(iLit)] == 1 )
      Vi_Push( p->vOrderF, iLit );
  assert( Vi_Size(p->vOrderF) == nFans );
  // try to remove fanins starting from the end of the list
  for ( n = Vi_Size(p->vOrderF)-1; n >= 0; n-- ) {
    int iFanin = Vi_Drop(p->vOrderF, n);
    word * pProd = Maig_TruthSimNodeSubset2( p, iObj, p->vOrderF, Vi_Size(p->vOrderF) );
    if ( !Tt_EqualOnCare(pCare, pFunc, pProd, p->nWords) )
      Vi_Push(p->vOrderF, iFanin);
  }
  assert( Vi_Size(p->vOrderF) >= 1 );
  // update the node if it is reduced
  if ( Vi_Size(p->vOrderF) < nFans ) {
    Maig_ObjDeref(p, iObj);
    Vi_Shrink( p->pvFans+iObj, 0 );
    Vi_ForEachEntry( p->vOrderF, iLit, k )
      Vi_PushOrder( p->pvFans+iObj, iLit );
    Maig_ObjRef(p, iObj);
    Maig_TruthUpdate( p, p->vTfo );
    if ( PRINT_DEBUG ) printf( "Reducing node %d fanin count from %d to %d.\n", iObj, nFans, Maig_ObjFaninNum(p, iObj) );
    return nFans-Vi_Size(p->vOrderF);
  }
  return 0;
}

/*************************************************************
                  high-level rewiring code
**************************************************************/

static inline vi * Rw_CreateOrder( maig * p )
{
  int i;
  Vi_Shrink( p->vOrder, 0 );
  Maig_ForEachNode( p, i )
    Vi_Push( p->vOrder, i );
  Vi_Randomize( p->vOrder );
  return p->vOrder;
}
static inline maig * Rw_Expand( maig * p, int nFaninAddLimitAll )
{
  int i, iNode, nAdded = 0;
  assert( nFaninAddLimitAll > 0 );
  vi * vOrder = Rw_CreateOrder( p );
  //printf( "Random order:  " ); Vi_Print( p->vOrder );
  Maig_TruthInitialize(p);
  Maig_InitializeRefs(p);
  Vi_ForEachEntry( vOrder, iNode, i )
    if ( (nAdded += Rw_ExpandOne(p, iNode, MinInt(Vi_Space(p->pvFans+iNode), nFaninAddLimitAll-nAdded))) >= nFaninAddLimitAll )
      break;
  assert( nAdded <= nFaninAddLimitAll );
  Maig_VerifyRefs(p);    
  return Maig_DupDfs(p);  
}
static inline maig * Rw_Reduce( maig * p )
{
  int i, iNode;
  vi * vOrder = Rw_CreateOrder( p );
  //printf( "Random order:  " ); Vi_Print( p->vOrder );
  Maig_TruthInitialize(p);
  Maig_InitializeRefs(p);
/*  
  int Value = Random_Num(0) % 16;
  if ( Value == 0 )
    Maig_ForEachNodeReverse( p, iNode )
      Rw_ReduceOne( p, iNode, 0, 0 );
  else if ( Value == 1 )
    Maig_ForEachNodeReverse( p, iNode )
      Rw_ReduceOne2( p, iNode, 0, 0 );      
  else if ( Value == 2 )
    Maig_ForEachNode( p, iNode )
      Rw_ReduceOne( p, iNode, 0, 0 );
  else if ( Value == 3 )
    Maig_ForEachNode( p, iNode )
      Rw_ReduceOne2( p, iNode, 0, 0 );      
  else if ( Value == 4 )
    Vi_ForEachEntry( vOrder, iNode, i )
      Rw_ReduceOne( p, iNode, 0, 0 );
  else 
    Vi_ForEachEntry( vOrder, iNode, i )
      Rw_ReduceOne2( p, iNode, 0, 0 );
*/
  // works best for final
  Vi_ForEachEntry( vOrder, iNode, i )
    Rw_ReduceOne2( p, iNode, 0, 0 );
  Maig_VerifyRefs(p);
  return Maig_DupStrash(p, 1, 1);
}


// storage for best AIGs
#define SAVE_NUM 8

int Rw_AddBest( maig ** pBests, int nBests, maig * pNew )
{
    if ( nBests < SAVE_NUM )
        pBests[nBests++] = pNew;
    else {
        assert( nBests == SAVE_NUM );
        int iNum = Random_Num(0) % SAVE_NUM;
        Maig_Free( pBests[iNum] );
        pBests[iNum] = pNew;
    }
    return nBests;
}
maig * Rw_ReadBest( maig ** pBests, int nBests )
{
    return pBests[Random_Num(0) % nBests];
}
void Rw_CleanBest( maig ** pBests, int nBests )
{
    for ( int i = 0; i < nBests; i++ )
        Maig_Free( pBests[i] );
}

static inline maig * Rw_PerformRewire( maig * p, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int fVerbose )
{
  maig * pBests[SAVE_NUM] = {NULL}; int nBests = 1;
  int i, k, n, iNode;
  iword clkTotal = Time_Clock(); 
  iword clk, times[3] = {0};
  maig * pTemp, * pNew; 
  maig * pBest = pBests[0] = Maig_Dup( p, 0 );
  int PrevBest = Maig_CountAnd2(pBest);
  int nAnd2, nAdded, nShared, nRemoved;
  for ( i = 0; i < nIters; i++ )
  {
    // expand
    clk      = Time_Clock(); 
    pNew     = Maig_DupMulti(pBest, nFaninMax, nGrowth);     
    nAnd2    = Maig_CountAnd2(pNew);
    pNew     = Rw_Expand(pTemp = pNew, nExpands); Maig_Free( pTemp );
    nAdded   = Maig_CountAnd2(pNew) - nAnd2;
    times[0]+= Time_Clock() - clk;
    // share
    clk      = Time_Clock(); 
    nAnd2    = Maig_CountAnd2(pNew);  
    pNew     = Rw_Share( pTemp = pNew, nDivs ); Maig_Free( pTemp );
    nShared  = nAnd2 - Maig_CountAnd2(pNew);
    times[1]+= Time_Clock() - clk;
    // reduce
    clk      = Time_Clock(); 
    nAnd2    = Maig_CountAnd2(pNew);  
    pNew     = Rw_Reduce( pTemp = pNew );   Maig_Free( pTemp );
    nRemoved = nAnd2 - Maig_CountAnd2(pNew);
    times[2]+= Time_Clock() - clk;
    // compare
    if ( 0 ) 
    {
      if ( Maig_CountAnd2(pBest) >= Maig_CountAnd2(pNew) )
        RW_SWAP( maig *, pBest, pNew )
      Maig_Free( pNew );
    }
    else 
    {
      if ( Maig_CountAnd2(pBest) < Maig_CountAnd2(pNew) )
        Maig_Free(pNew);
      else if ( Maig_CountAnd2(pBest) == Maig_CountAnd2(pNew) )
        nBests = Rw_AddBest(pBests, nBests, pNew);
      else {
        Rw_CleanBest(pBests, nBests);
        pBests[0] = pNew;
        nBests = 1;
      }
      pBest = Rw_ReadBest(pBests, nBests);
    }
    // report
    if ( PrevBest > Maig_CountAnd2(pBest) )
    {
        printf( "Iteration %5d :  ", i );
        printf( "Added =%4d  ",     nAdded );
        printf( "Shared =%4d  ",    nShared );
        printf( "Removed =%4d  ",   nRemoved );
        printf( "Best =%5d",        Maig_CountAnd2(pBest) );
        printf( "\n" );
        PrevBest = Maig_CountAnd2(pBest);
    }    
  }
  pBest = Maig_Dup( pBest, 0 );
  Rw_CleanBest( pBests, nBests );
  Time_Print( "Total solving time", Time_Clock() - clkTotal );
  printf( "  (" );
  printf( "Expand = %.1f %%  ", 100.0*times[0]/(Time_Clock() - clkTotal) );
  printf( "Share = %.1f %%  ",  100.0*times[1]/(Time_Clock() - clkTotal) );
  printf( "Reduce = %.1f %%",   100.0*times[2]/(Time_Clock() - clkTotal) );
  printf( ")\n" );
  return pBest;
}

Mini_Aig_t * Rw_Transform( Mini_Aig_t * pAig, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int fVerbose )
{
  if ( 1 )
  {
    maig * p = Maig_FromMiniAig( pAig );
    maig * pNew = Rw_PerformRewire( p, nIters, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, fVerbose );
    pAig = Maig_ToMiniAig( pNew );
    Maig_Free( pNew );
    Maig_Free( p );
  }
  else
  {
    maig * p = Maig_FromMiniAig( pAig );                  // Maig_Print( p );
    maig * pNew1 = Maig_DupMulti(p, nFaninMax, nGrowth);  // Maig_Print( pNew1 );
    maig * pNew2 = Rw_Expand(pNew1, nExpands);            // Maig_Print( pNew2 );
    maig * pNew3 = Rw_Reduce(pNew2);                      // Maig_Print( pNew3 );
    pAig = Maig_ToMiniAig( pNew3 );
    Maig_Free( pNew2 );
    Maig_Free( pNew1 );
    Maig_Free( p );
  }
  return pAig;
}

/*************************************************************
                    main() procedure
**************************************************************/

void Rw_OutputFilename( char * pIn, char * pOut )
{
  int i, k = 0;
  for ( i = 0; i < strlen(pIn); i++ ) {
    if ( pIn[i] == '.' )
      pOut[k++] = '_', pOut[k++] = 'o', pOut[k++] = 'u', pOut[k++] = 't';
    pOut[k++] = pIn[i];
  }
  pOut[k] = 0;
}
int main(int argc, char ** argv)
{
    int nIters = 1000, nExpands = 100, nGrowth = 3, nDivs = 4, nFaninMax = 4, nSeed = 1, nTimeOut = 0, fVerbose = 0;
    if ( argc == 1 )
    {
        printf( "usage:  %s [-IEGDFSTV <num>] <file.aig>\n", argv[0] );
        printf( "                   this program performs AIG re-wiring\n" );
        printf( "\n" );     
        printf( "      -I <num>  :  the number of iterations [default = %d]\n",                 nIters );          
        printf( "      -E <num>  :  the number of nodes to expand [default = %d]\n",            nExpands );        
        printf( "      -G <num>  :  the number of fanins that can be added [default = %d]\n",   nGrowth );            
        printf( "      -D <num>  :  the number of shared divisors to extract [default = %d]\n", nDivs );            
        printf( "      -F <num>  :  the limit on the fanin count at a node [default = %d]\n",   nFaninMax );            
        printf( "      -S <num>  :  the random seed [default = %d]\n",                          nSeed );
        printf( "      -T <num>  :  the timeout in seconds [default = unused]\n" );  
        printf( "      -V <num>  :  the verbosity level [default = %d]\n",                      fVerbose );                        
        printf( "    <file.aig>  :  the input file name\n" );
        return 1;
    }
    else
    {
        Mini_Aig_t * pAig = NULL, * pNew = NULL;
        char * pFileName = argv[argc-1], pFileNameOut[1000]; 
        Rw_OutputFilename( pFileName, pFileNameOut );
        for ( int c = 1; c < argc-1; c++ ) {
               if ( argv[c][0] == '-' && argv[c][1] == 'I' )
            nIters = atoi(argv[++c]);
          else if ( argv[c][0] == '-' && argv[c][1] == 'E' )
            nExpands = atoi(argv[++c]);
          else if ( argv[c][0] == '-' && argv[c][1] == 'G' )
            nGrowth = atoi(argv[++c]);            
          else if ( argv[c][0] == '-' && argv[c][1] == 'D' )
            nDivs = atoi(argv[++c]);            
          else if ( argv[c][0] == '-' && argv[c][1] == 'F' )
            nFaninMax = atoi(argv[++c]);            
          else if ( argv[c][0] == '-' && argv[c][1] == 'S' )
            nSeed = atoi(argv[++c]);
          else if ( argv[c][0] == '-' && argv[c][1] == 'T' )
            nTimeOut = atoi(argv[++c]);
          else if ( argv[c][0] == '-' && argv[c][1] == 'V' )
            fVerbose = atoi(argv[++c]);
          else {
            printf( "Unknown command-line option (%s).\n", argv[c] );
            return 1;
          }
        }
        printf( "Parameters:  Iters = %d  Expand = %d  Growth = %d  Divs = %d  FaninMax = %d  Seed = %d  Timeout = %d  Verbose = %d\n", 
          nIters, nExpands, nGrowth, nDivs, nFaninMax, nSeed, nTimeOut, fVerbose );          
        Random_Num( nSeed );
        pAig = Mini_AigerRead( pFileName, 1 );
        if ( pAig == NULL )
          return 1;
        Mini_AigPrintStats( pAig );
        pNew = Rw_Transform( pAig, nIters, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, fVerbose );
        if ( pNew == NULL )
          printf( "The output AIG is not produced.\n" );
        else {
          Mini_AigPrintStats( pNew );
          Mini_AigerWrite( pFileNameOut, pNew, 1 );
          Mini_AigStop( pNew );
        }
        Mini_AigStop( pAig );
        return 1;
    }
}

/*************************************************************
                     end of file
**************************************************************/
