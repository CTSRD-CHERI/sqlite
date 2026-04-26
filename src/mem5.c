/*
** 2007 October 14
**
** The author disclaims copyright to this source code.  In place of
** a legal notice, here is a blessing:
**
**    May you do good and not evil.
**    May you find forgiveness for yourself and forgive others.
**    May you share freely, never taking more than you give.
**
*************************************************************************
** This file contains the C functions that implement a memory
** allocation subsystem for use by SQLite. 
**
** This version of the memory allocation subsystem omits all
** use of malloc(). The application gives SQLite a block of memory
** before calling sqlite3_initialize() from which allocations
** are made and returned by the xMalloc() and xRealloc() 
** implementations. Once sqlite3_initialize() has been called,
** the amount of memory available to SQLite is fixed and cannot
** be changed.
**
** This version of the memory allocation subsystem is included
** in the build only if SQLITE_ENABLE_MEMSYS5 is defined.
**
** This memory allocator uses the following algorithm:
**
**   1.  All memory allocation sizes are rounded up to a power of 2.
**
**   2.  If two adjacent free blocks are the halves of a larger block,
**       then the two blocks are coalesced into the single larger block.
**
**   3.  New memory is allocated from the first available free block.
**
** This algorithm is described in: J. M. Robson. "Bounds for Some Functions
** Concerning Dynamic Storage Allocation". Journal of the Association for
** Computing Machinery, Volume 21, Number 8, July 1974, pages 491-499.
** 
** Let n be the size of the largest allocation divided by the minimum
** allocation size (after rounding all sizes up to a power of 2.)  Let M
** be the maximum amount of memory ever outstanding at one time.  Let
** N be the total amount of memory available for allocation.  Robson
** proved that this memory allocator will never breakdown due to 
** fragmentation as long as the following constraint holds:
**
**      N >=  M*(1 + log2(n)/2) - n + 1
**
** The sqlite3_status() logic tracks the maximum values of n and M so
** that an application can, at any time, verify this constraint.
*/
#include "sqliteInt.h"
#include <sys/param.h>
#include <sys/ktrace.h>
#include <sys/mman.h>
#include <sys/tree.h>
#include <sys/resource.h>
#include <sys/cpuset.h>
#include <sys/queue.h>
#include <sys/sysctl.h>

#include <cheri/cheri.h>
#include <cheri/cheric.h>
#include <cheri/revoke.h>
#include <cheri/libcaprevoke.h>

#include <machine/vmparam.h>

#include <assert.h>
#include <dlfcn.h>
#include <errno.h>
#include <inttypes.h>
#include <malloc_np.h>
#include <pthread.h>
#include <pthread_np.h>
#include <stdatomic.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <sys/elf.h>


#define NESTED_TEMPORAL 1

/*
** This version of the memory allocator is used only when 
** SQLITE_ENABLE_MEMSYS5 is defined.
*/
#ifdef SQLITE_ENABLE_MEMSYS5

/*
** A minimum allocation is an instance of the following structure.
** Larger allocations are an array of these structures where the
** size of the array is a power of 2.
**
** The size of this object must be a power of two.  That fact is
** verified in memsys5Init().
*/

static inline uint64_t
cheri_revoke_get_cyc(void)
{
#if defined(__riscv)
	return (__builtin_readcyclecounter());
#elif defined(__aarch64__)
	uint64_t _val;
	__asm __volatile("mrs %0, cntvct_el0" : "=&r" (_val));
	return (_val);
#else
	return (0);
#endif
}



static inline void cclear(void * a){
  asm volatile("cclearpoison %0, 0(%1)": :"C"(a),"C"(a));
}

static inline void
clear_region(void *mem, size_t len)
{
	static const size_t ZERO_THRESHOLD = 64;

	/*
	 * For small regions that are qword-multiple-sized, use writes to avoid
	 * memset call.  Alignment should be good in normal cases.
	 */
	if ((len <= ZERO_THRESHOLD) && (len % sizeof(uint64_t) == 0)) {
		for (size_t i = 0; i < (len / sizeof(uint64_t)); i++) {
			/*
			 * volatile needed to avoid memset call by
			 * compiler "optimization"
			 */
			((volatile uint64_t *)mem)[i] = 0;
		}
	} else {
		memset(mem, 0, len);
	}
}


typedef struct Mem5Link Mem5Link;
struct Mem5Link {
  int next;       /* Index of next free chunk */
  int prev;       /* Index of previous free chunk */
};

static void* mem5_heap_cap;
static uintptr_t mem5_heap_base;

/*
** Maximum size of any allocation is ((1<<LOGMAX)*mem5.szAtom). Since
** mem5.szAtom is always at least 8 and 32-bit integers are used,
** it is not actually possible to reach this limit.
*/
#define LOGMAX 30

/*
** Masks used for mem5.aCtrl[] elements.
*/
#define CTRL_LOGSIZE  0x1f    /* Log2 Size of this block */
#define CTRL_FREE     0x20    /* True if not checked out */

/*
** All of the static variables used by this module are collected
** into a single structure named "mem5".  This is to keep the
** static variables organized and to reduce namespace pollution
** when this module is combined with other in the amalgamation.
*/
static SQLITE_WSD struct Mem5Global {
  /*
  ** Memory available for allocation
  */
  int szAtom;      /* Smallest possible allocation in bytes */
  int nBlock;      /* Number of szAtom sized blocks in zPool */
  u8 *zPool;       /* Memory available to be allocated */
  
  /*
  ** Mutex to control access to the memory allocation subsystem.
  */
  sqlite3_mutex *mutex;

#if defined(SQLITE_DEBUG) || defined(SQLITE_TEST)
  /*
  ** Performance statistics
  */
  u64 nAlloc;         /* Total number of calls to malloc */
  u64 totalAlloc;     /* Total of all malloc calls - includes internal frag */
  u64 totalExcess;    /* Total internal fragmentation */
  u32 currentOut;     /* Current checkout, including internal fragmentation */
  u32 currentCount;   /* Current number of distinct checkouts */
  u32 maxOut;         /* Maximum instantaneous currentOut */
  u32 maxCount;       /* Maximum instantaneous currentCount */
  u32 maxRequest;     /* Largest allocation (exclusive of internal frag) */
#endif
  
  /*
  ** Lists of free blocks.  aiFreelist[0] is a list of free blocks of
  ** size mem5.szAtom.  aiFreelist[1] holds blocks of size szAtom*2.
  ** aiFreelist[2] holds free blocks of size szAtom*4.  And so forth.
  */
  int aiFreelist[LOGMAX+1];

  /*
  ** Space for tracking which blocks are checked out and the size
  ** of each block.  One byte per block.
  */
  u8 *aCtrl;

} mem5;

/*
** Access the static variable through a macro for SQLITE_OMIT_WSD.
*/
#define mem5 GLOBAL(struct Mem5Global, mem5)

/*
** Assuming mem5.zPool is divided up into an array of Mem5Link
** structures, return a pointer to the idx-th such link.
*/
//#define MEM5LINK(idx) ((Mem5Link *)(&mem5.zPool[(idx)*mem5.szAtom]))
static Mem5Link *mem5_link; 
//#define MEM5LINK(idx) ((Mem5Link *)cheri_setoffset(mem5_heap_cap, (idx)*mem5.szAtom))

/*
** Unlink the chunk at mem5.aPool[i] from list it is currently
** on.  It should be found on mem5.aiFreelist[iLogsize].
*/
static void memsys5Unlink(int i, int iLogsize){
  int next, prev;
  assert( i>=0 && i<mem5.nBlock );
  assert( iLogsize>=0 && iLogsize<=LOGMAX );
  assert( (mem5.aCtrl[i] & CTRL_LOGSIZE)==iLogsize );

  next = mem5_link[i].next; //MEM5LINK(i)->next;
  prev = mem5_link[i].prev; //MEM5LINK(i)->prev;
  if( prev<0 ){
    mem5.aiFreelist[iLogsize] = next;
  }else{
    //MEM5LINK(prev)->next = next;
    mem5_link[prev].next = next; 
  }
  if( next>=0 ){
    //MEM5LINK(next)->prev = prev;
    mem5_link[next].prev = prev;
  }
}

/*
** Link the chunk at mem5.aPool[i] so that is on the iLogsize
** free list.
*/
static void memsys5Link(int i, int iLogsize){
  int x;
  assert( sqlite3_mutex_held(mem5.mutex) );
  assert( i>=0 && i<mem5.nBlock );
  assert( iLogsize>=0 && iLogsize<=LOGMAX );
  assert( (mem5.aCtrl[i] & CTRL_LOGSIZE)==iLogsize );

  //x = MEM5LINK(i)->next = mem5.aiFreelist[iLogsize];
  //MEM5LINK(i)->prev = -1;
  x = mem5_link[i].next = mem5.aiFreelist[iLogsize];
  mem5_link[i].prev = -1;
  if( x>=0 ){
    assert( x<mem5.nBlock );
    //MEM5LINK(x)->prev = i;
    mem5_link[x].prev = i;
  }
  mem5.aiFreelist[iLogsize] = i;
}

/*
** Obtain or release the mutex needed to access global data structures.
*/
static void memsys5Enter(void){
  sqlite3_mutex_enter(mem5.mutex);
}
static void memsys5Leave(void){
  sqlite3_mutex_leave(mem5.mutex);
}

/*
** Return the size of an outstanding allocation, in bytes.
** This only works for chunks that are currently checked out.
*/
static int memsys5Size(void *p){
  //int iSize, i;
  //assert( p!=0 );
  //i = (int)(((u8 *)p-mem5.zPool)/mem5.szAtom);
  //assert( i>=0 && i<mem5.nBlock );
  //iSize = mem5.szAtom * (1 << (mem5.aCtrl[i]&CTRL_LOGSIZE));
  //return iSize;
  uintptr_t addr = cheri_getaddress(p);
  uintptr_t base = mem5_heap_base; 
  
  uintptr_t offset = addr - base; 
  offset &= ~(mem5.szAtom -1);
 
  int i = offset / mem5.szAtom;
  int iSize = mem5.szAtom  * (1 << (mem5.aCtrl[i] & CTRL_LOGSIZE));
  return iSize;
}

/*
** Return a block of memory of at least nBytes in size.
** Return NULL if unable.  Return NULL if nBytes==0.
**
** The caller guarantees that nByte is positive.
**
** The caller has obtained a mutex prior to invoking this
** routine so there is never any chance that two or more
** threads can be in this routine at the same time.
*/
static void *memsys5MallocUnsafe(int nByte){
  int i;           /* Index of a mem5.aPool[] slot */
  int iBin;        /* Index into mem5.aiFreelist[] */
  int iFullSz;     /* Size of allocation rounded up to power of 2 */
  int iLogsize;    /* Log2 of iFullSz/POW2_MIN */

  /* nByte must be a positive */
  assert( nByte>0 );

  /* No more than 1GiB per allocation */
  if( nByte > 0x40000000 ) return 0;

#if defined(SQLITE_DEBUG) || defined(SQLITE_TEST)
  /* Keep track of the maximum allocation request.  Even unfulfilled
  ** requests are counted */
  if( (u32)nByte>mem5.maxRequest ){
    mem5.maxRequest = nByte;
  }
#endif


  /* Round nByte up to the next valid power of two */
  for(iFullSz=mem5.szAtom,iLogsize=0; iFullSz<nByte; iFullSz*=2,iLogsize++){}

  /* Make sure mem5.aiFreelist[iLogsize] contains at least one free
  ** block.  If not, then split a block of the next larger power of
  ** two in order to create a new free block of size iLogsize.
  */
  for(iBin=iLogsize; iBin<=LOGMAX && mem5.aiFreelist[iBin]<0; iBin++){}
  if( iBin>LOGMAX ){
    testcase( sqlite3GlobalConfig.xLog!=0 );
    sqlite3_log(SQLITE_NOMEM, "failed to allocate %u bytes", nByte);
    //printf("malloc early return\n");
    //for(int k =0 ; k < LOGMAX ; k++)
    //  printf("freelist[%d] = %d\n", k, mem5.aiFreelist[k]);
    return 0;
  }
  i = mem5.aiFreelist[iBin];
  memsys5Unlink(i, iBin);
  while( iBin>iLogsize ){
    int newSize;

    iBin--;
    newSize = 1 << iBin;
    mem5.aCtrl[i+newSize] = CTRL_FREE | iBin;
    memsys5Link(i+newSize, iBin);
  }
  mem5.aCtrl[i] = iLogsize;

#if defined(SQLITE_DEBUG) || defined(SQLITE_TEST)
  /* Update allocator performance statistics. */
  mem5.nAlloc++;
  mem5.totalAlloc += iFullSz;
  mem5.totalExcess += iFullSz - nByte;
  mem5.currentCount++;
  mem5.currentOut += iFullSz;
  if( mem5.maxCount<mem5.currentCount ) mem5.maxCount = mem5.currentCount;
  if( mem5.maxOut<mem5.currentOut ) mem5.maxOut = mem5.currentOut;
#endif

#ifdef SQLITE_DEBUG
  /* Make sure the allocated memory does not assume that it is set to zero
  ** or retains a value from a previous allocation */
  //memset(&mem5.zPool[i*mem5.szAtom], 0xAA, iFullSz);
#endif
  if(!cheri_gettag(mem5.zPool))
    printf("mem5.zPool is not tagged");
  /* Return a pointer to the allocated memory. */
  //return (void*)&mem5.zPool[i*mem5.szAtom];
  void* p =  cheri_setoffset(mem5_heap_cap, i*mem5.szAtom);
  //clear_region(mem5_heap_cap + i*mem5.szAtom , iFullSz);
  //if(cheri_gettag(p))
  //  printf("p has tag\n");
  //else 
  //  printf("p has no tag\n");
  assert(cheri_gettag(p));
  return p;
}

/*
** Free an outstanding memory allocation.
*/
static void memsys5FreeUnsafe(void *pOld){
  u32 size, iLogsize;
  int iBlock;

  /* Set iBlock to the index of the block pointed to by pOld in 
  ** the array of mem5.szAtom byte blocks pointed to by mem5.zPool.
  */
  uintptr_t addr = cheri_getaddress(pOld);
  uintptr_t base = mem5_heap_base;
  iBlock = (addr - base) /mem5.szAtom;
  //iBlock = (int)(((u8 *)pOld-mem5.zPool)/mem5.szAtom);

  /* Check that the pointer pOld points to a valid, non-free block. */
  assert( iBlock>=0 && iBlock<mem5.nBlock );
  assert( ((u8 *)pOld-mem5.zPool)%mem5.szAtom==0 );
  assert( (mem5.aCtrl[iBlock] & CTRL_FREE)==0 );

  iLogsize = mem5.aCtrl[iBlock] & CTRL_LOGSIZE;
  size = 1<<iLogsize;
  assert( iBlock+size-1<(u32)mem5.nBlock );

  mem5.aCtrl[iBlock] |= CTRL_FREE;
  mem5.aCtrl[iBlock+size-1] |= CTRL_FREE;

#if defined(SQLITE_DEBUG) || defined(SQLITE_TEST)
  assert( mem5.currentCount>0 );
  assert( mem5.currentOut>=(size*mem5.szAtom) );
  mem5.currentCount--;
  mem5.currentOut -= size*mem5.szAtom;
  assert( mem5.currentOut>0 || mem5.currentCount==0 );
  assert( mem5.currentCount>0 || mem5.currentOut==0 );
#endif

  mem5.aCtrl[iBlock] = CTRL_FREE | iLogsize;
  while( ALWAYS(iLogsize<LOGMAX) ){
    int iBuddy;
    if( (iBlock>>iLogsize) & 1 ){
      iBuddy = iBlock - size;
      assert( iBuddy>=0 );
    }else{
      iBuddy = iBlock + size;
      if( iBuddy>=mem5.nBlock ) break;
    }
    if( mem5.aCtrl[iBuddy]!=(CTRL_FREE | iLogsize) ) break;
    memsys5Unlink(iBuddy, iLogsize);
    iLogsize++;
    if( iBuddy<iBlock ){
      mem5.aCtrl[iBuddy] = CTRL_FREE | iLogsize;
      mem5.aCtrl[iBlock] = 0;
      iBlock = iBuddy;
    }else{
      mem5.aCtrl[iBlock] = CTRL_FREE | iLogsize;
      mem5.aCtrl[iBuddy] = 0;
    }
    size *= 2;
  }

#ifdef SQLITE_DEBUG
  /* Overwrite freed memory with the 0x55 bit pattern to verify that it is
  ** not used after being freed */
  memset(&mem5.zPool[iBlock*mem5.szAtom], 0x55, size);
#endif

  memsys5Link(iBlock, iLogsize);
}

#define QUARANTINE_MAX 4096
#define QUARANTINE_EPOCH_DELAY 2

struct quarantine_entry{
  void * ptr; 
  size_t size; 
  //cheri_revoke_epoch_t epoch;
};

static struct quarantine_entry quarantine[QUARANTINE_MAX];
static size_t q_head = 0;
static size_t q_tail = 0;
static size_t q_count =0;
static size_t total_alloc_size = 0;
static size_t quarantine_size = 0;
static size_t revocation_count = 0;

/*
** Allocate nBytes of memory.
*/

void * cclearpoisonperm(void * a){
	void *ptr ;
	uint64_t mask = ~(1ull << 12);
    ptr = cheri_andperm(a, mask);

	return ptr;
}

static void *memsys5Malloc(int nBytes){
  sqlite3_int64 *p = 0;
  
  if( nBytes>0 ){
    memsys5Enter();
    p = memsys5MallocUnsafe(nBytes);
    memsys5Leave();
  }
  //if(!cheri_gettag(p))
  //  printf("malloc p has no tag %d\n", nBytes);

  

  size_t alloc_size = memsys5Size(p);
#ifdef NESTED_TEMPORAL
  total_alloc_size += alloc_size;
  clear_region(cheri_setoffset(mem5_heap_cap, cheri_getoffset(p)), alloc_size);
  //for(int i = 0 ; i< alloc_size; i+=16){
  //  void *addr = (char*) p + i;
  //  //cclear(addr);
  //  *(volatile uint64_t*) addr = 0;
  //  //cclear((void*)p+i);
  //}
#endif 
  void *bounded_p =  cheri_setbounds((void*)p, alloc_size);
  //printf("alloc_size =%zu\n", alloc_size);
  //printf("cheri_getlen %lu\n", cheri_getlen(bounded_p));
  //bounded_p = cclearpoisonperm(bounded_p);
  return bounded_p; 
}

/*
** Free memory.
**
** The outer layer memory allocator prevents this routine from
** being called with pPrior==0.
*/

static inline void cpoison(char * a){
  asm volatile("cpoison %0, 0(%1)": :"C"(a),"C"(a));
}

static void quarantine_flush(void){
  //cheri_revoke_epoch_t now = cheri_revoke_st_get_epoch();
  //revocation_count+=1;
  //printf("revocation_count %d\n", (int)revocation_count);
  while(q_count > 0){
    struct quarantine_entry *e = &quarantine[q_head];

    //if((now - e-> epoch) < QUARANTINE_EPOCH_DELAY ){
    //  break;
    //}
    memsys5Enter();
    memsys5FreeUnsafe(e -> ptr);
    memsys5Leave();  

    q_head = (q_head + 1) % QUARANTINE_MAX;
    size_t current_size = e->size;
    quarantine_size = quarantine_size - current_size;
    total_alloc_size -= current_size;
    q_count --;
  }
}
static void quarantine_revoke(void){
  	(void)cheri_revoke(CHERI_REVOKE_ASYNC, 0, NULL);
    quarantine_flush();

}


static void check_and_flush(void){
  if (total_alloc_size < 1024 * 1024*16)
    return ;

  if(quarantine_size*4  >= total_alloc_size){
    //quarantine_flush();
    quarantine_revoke();
  }
}


static void quarantine_insert(void* base, size_t size){
  //cheri_revoke_epoch_t now = cheri_revoke_get_epoch();
  if (q_count == QUARANTINE_MAX){
    quarantine_flush();
  }
  
  quarantine[q_tail].ptr = base;
  quarantine[q_tail].size = size;
  //quarantine[q_tail].epoch = now;

  q_tail = (q_tail + 1) % QUARANTINE_MAX;
  quarantine_size += size;
  q_count +=1;
}


static void memsys5Free(void *pPrior){
  assert( pPrior!=0 );
  //fprintf(stderr, "memsys5Free\n");

  uintptr_t heap_base = cheri_getaddress(mem5_heap_cap);
  uintptr_t addr      = cheri_getaddress(pPrior);

  uintptr_t offset = addr - heap_base; 
  offset &= ~(mem5.szAtom -1);
  void *p = cheri_setoffset(mem5_heap_cap, offset);

  memsys5Enter();
#ifdef NESTED_TEMPORAL
  int iBlock = offset/ mem5.szAtom;
  int iLogsize = mem5.aCtrl[iBlock] &CTRL_LOGSIZE;
  size_t size = mem5.szAtom * (1 << iLogsize);
  void *bounded = cheri_setbounds(p, size);
  quarantine_insert(p, size);
  for(size_t i =0 ; i< size;i+=16)
    cpoison(bounded + i);
  check_and_flush();
#else 
  memsys5FreeUnsafe(p);
#endif 
  memsys5Leave();  
}

/*
** Change the size of an existing memory allocation.
**
** The outer layer memory allocator prevents this routine from
** being called with pPrior==0.  
**
** nBytes is always a value obtained from a prior call to
** memsys5Round().  Hence nBytes is always a non-negative power
** of two.  If nBytes==0 that means that an oversize allocation
** (an allocation larger than 0x40000000) was requested and this
** routine should return 0 without freeing pPrior.
*/
static void *memsys5Realloc(void *pPrior, int nBytes){
  int nOld;
  void *p;
  assert( pPrior!=0 );
  assert( (nBytes&(nBytes-1))==0 );  /* EV: R-46199-30249 */
  assert( nBytes>=0 );
  if( nBytes==0 ){
    return 0;
  }
  nOld = memsys5Size(pPrior);
  if( nBytes<=nOld ){
    return pPrior;
  }
  p = memsys5Malloc(nBytes);
  if( p ){
    memcpy(p, pPrior, nOld);
    memsys5Free(pPrior);
  }
  return p;
}

/*
** Round up a request size to the next valid allocation size.  If
** the allocation is too large to be handled by this allocation system,
** return 0.
**
** All allocations must be a power of two and must be expressed by a
** 32-bit signed integer.  Hence the largest allocation is 0x40000000
** or 1073741824 bytes.
*/
static int memsys5Roundup(int n){
  int iFullSz;
  if( n > 0x40000000 ) return 0;
  for(iFullSz=mem5.szAtom; iFullSz<n; iFullSz *= 2);
  return iFullSz;
}

/*
** Return the ceiling of the logarithm base 2 of iValue.
**
** Examples:   memsys5Log(1) -> 0
**             memsys5Log(2) -> 1
**             memsys5Log(4) -> 2
**             memsys5Log(5) -> 3
**             memsys5Log(8) -> 3
**             memsys5Log(9) -> 4
*/
static int memsys5Log(int iValue){
  int iLog;
  for(iLog=0; (iLog<(int)((sizeof(int)*8)-1)) && (1<<iLog)<iValue; iLog++);
  return iLog;
}

/*
** Initialize the memory allocator.
**
** This routine is not threadsafe.  The caller must be holding a mutex
** to prevent multiple threads from entering at the same time.
*/
static int memsys5Init(void *NotUsed){
  int ii;            /* Loop counter */
  int nByte;         /* Number of bytes of memory available to this allocator */
  u8 *zByte;         /* Memory usable by this allocator */
  int nMinLog;       /* Log base 2 of minimum allocation size in bytes */
  int iOffset;       /* An offset into mem5.aCtrl[] */

  printf("INIT\n");
  printf("nHeap= %d\n", sqlite3GlobalConfig.nHeap);
  printf("pHeap= %p\n", sqlite3GlobalConfig.pHeap);
  printf("mnReq= %d\n", sqlite3GlobalConfig.mnReq);

  UNUSED_PARAMETER(NotUsed);

  /* For the purposes of this routine, disable the mutex */
  mem5.mutex = 0;

  /* The size of a Mem5Link object must be a power of two.  Verify that
  ** this is case.
  */
  assert( (sizeof(Mem5Link)&(sizeof(Mem5Link)-1))==0 );

  nByte = sqlite3GlobalConfig.nHeap;
  zByte = (u8*)sqlite3GlobalConfig.pHeap;
  assert( zByte!=0 );  /* sqlite3_config() does not allow otherwise */

  /* boundaries on sqlite3GlobalConfig.mnReq are enforced in sqlite3_config() */
  nMinLog = memsys5Log(sqlite3GlobalConfig.mnReq);
  mem5.szAtom = (1<<nMinLog);
  while( (int)sizeof(Mem5Link)>mem5.szAtom ){
    mem5.szAtom = mem5.szAtom << 1;
  }

  mem5.nBlock = (nByte / (mem5.szAtom+sizeof(u8)));
  mem5.zPool = zByte;
  mem5_heap_cap = cheri_setbounds(zByte, nByte); 
  mem5_heap_base = cheri_getaddress(mem5_heap_cap);
  assert(cheri_gettag(mem5_heap_cap));

  //printf("heap tag =%d\n", cheri_gettag(mem5_heap_cap));
  mem5.aCtrl = (u8 *)&mem5.zPool[mem5.nBlock*mem5.szAtom];
  //mem5.aCtrl = cheri_setoffset(mem5_heap_cap, mem5.nBlock * mem5.szAtom);
  for(ii=0; ii<=LOGMAX; ii++){
    mem5.aiFreelist[ii] = -1;
  }


  void *raw = mmap(NULL, mem5.nBlock* sizeof(Mem5Link), PROT_READ | PROT_WRITE, MAP_ANON | MAP_PRIVATE, -1, 0);
  if(raw == MAP_FAILED) return SQLITE_NOMEM; 
  memset(raw, 0, mem5.nBlock * sizeof(Mem5Link));
  mem5_link = cheri_setbounds(raw, mem5.nBlock * sizeof(Mem5Link));
  if(!cheri_gettag(mem5_link))
    printf("mem5_link has no tag\n");
  iOffset = 0;
  for(ii=LOGMAX; ii>=0; ii--){
    int nAlloc = (1<<ii);
    if( (iOffset+nAlloc)<=mem5.nBlock ){
      mem5.aCtrl[iOffset] = ii | CTRL_FREE;
      memsys5Link(iOffset, ii);
      iOffset += nAlloc;
    }
    assert((iOffset+nAlloc)>mem5.nBlock);
  }

  /* If a mutex is required for normal operation, allocate one */
  if( sqlite3GlobalConfig.bMemstat==0 ){
    mem5.mutex = sqlite3MutexAlloc(SQLITE_MUTEX_STATIC_MEM);
  }

  //for(int k=0; k <= LOGMAX ;k++)
  //  printf("INIT freelist [%d]= %d\n", k, mem5.aiFreelist[k]);
  //printf("nByte =%d szAtmo=%d nBlock=%d\n", nByte, mem5.szAtom, mem5.nBlock);
  //app_quarantine = mmap(NULL, sizeof(struct sql_quarantine), PROT_READ | PROT_WRITE, MAP_ANON, -1, 0);
  //printf("app_quarantine tag=%d perms %lx\n", cheri_gettag(app_quarantine), cheri_getperm(app_quarantine));

  printf("heap len =%lu, expected = %d\n", cheri_getlen(mem5_heap_cap), nByte);
  return SQLITE_OK;
}

/*
** Deinitialize this module.
*/
static void memsys5Shutdown(void *NotUsed){
  UNUSED_PARAMETER(NotUsed);
  mem5.mutex = 0;
  return;
}

#ifdef SQLITE_TEST
/*
** Open the file indicated and write a log of all unfreed memory 
** allocations into that log.
*/
void sqlite3Memsys5Dump(const char *zFilename){
  FILE *out;
  int i, j, n;
  int nMinLog;

  if( zFilename==0 || zFilename[0]==0 ){
    out = stdout;
  }else{
    out = fopen(zFilename, "w");
    if( out==0 ){
      fprintf(stderr, "** Unable to output memory debug output log: %s **\n",
                      zFilename);
      return;
    }
  }
  memsys5Enter();
  nMinLog = memsys5Log(mem5.szAtom);
  for(i=0; i<=LOGMAX && i+nMinLog<32; i++){
    for(n=0, j=mem5.aiFreelist[i]; j>=0; j = mem5_link[j].next, n++){}
    fprintf(out, "freelist items of size %d: %d\n", mem5.szAtom << i, n);
  }
  fprintf(out, "mem5.nAlloc       = %llu\n", mem5.nAlloc);
  fprintf(out, "mem5.totalAlloc   = %llu\n", mem5.totalAlloc);
  fprintf(out, "mem5.totalExcess  = %llu\n", mem5.totalExcess);
  fprintf(out, "mem5.currentOut   = %u\n", mem5.currentOut);
  fprintf(out, "mem5.currentCount = %u\n", mem5.currentCount);
  fprintf(out, "mem5.maxOut       = %u\n", mem5.maxOut);
  fprintf(out, "mem5.maxCount     = %u\n", mem5.maxCount);
  fprintf(out, "mem5.maxRequest   = %u\n", mem5.maxRequest);
  memsys5Leave();
  if( out==stdout ){
    fflush(stdout);
  }else{
    fclose(out);
  }
}
#endif

/*
** This routine is the only routine in this file with external 
** linkage. It returns a pointer to a static sqlite3_mem_methods
** struct populated with the memsys5 methods.
*/
const sqlite3_mem_methods *sqlite3MemGetMemsys5(void){
  static const sqlite3_mem_methods memsys5Methods = {
     memsys5Malloc,
     memsys5Free,
     memsys5Realloc,
     memsys5Size,
     memsys5Roundup,
     memsys5Init,
     memsys5Shutdown,
     0
  };
  return &memsys5Methods;
}

#endif /* SQLITE_ENABLE_MEMSYS5 */
