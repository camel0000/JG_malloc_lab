/*
* Explicit_malloc_lab
*/

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "malloc-lab team1",
    /* First member's full name */
    "Cho Min Gi",
    /* First member's email address */
    "camel0000@naver.com",
    /* Second member's full name (leave blank if none) */
    "An Sung Beom",
    /* Second member's email address (leave blank if none) */

    /* Third member's full name (leave blank if none) */
    "Lim Hye Jung",
    /* Third member's email address (leave blank if none) */

};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */       // word 사이즈
#define DSIZE 8             /* Double word size (bytes) */                  // double word 사이즈
#define CHUNKSIZE (1<<12)   /* Extend heap by this amount (bytes) */        // 초기 free block과 heap extension을 위한 기본 크기 CHUNKSIZE

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)                       // 주소 조정을 위한(?) 조정할 사이즈 정의(?)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))                                 // size_t 구조체의 size 정의

#define MAX(x, y) ((x) > (y) ? (x) : (y))                                   // 대소 비교 정의(max 값 리턴)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))                              // 크기와 할당 비트를 통합, header & footer에 저장할 수 있는 값 리턴

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))                              // 인자 p가 참조하는 워드를 읽어, 리턴
#define PUT(p, val)     (*(unsigned int *)(p) = (val))                      // 인자 p가 참조하는 워드에 val을 저장

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)                                     // 주소 p에 있는 header or footer의 size와 할당 비트를 리턴
#define GET_ALLOC(p)    (GET(p) & 0x1)                                      // 위와 동일

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)                              // block header를 가리키는 포인터 리턴
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)         // block footer를 가리키는 포인터 리턴

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   // 다음 블록의 블록 포인터 리턴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   // 이전 블록의 블록 포인터 리턴

#define PRED_LOC(bp) HDRP(bp)+WSIZE // prev가 들어갈 주소
#define SUCC_LOC(bp) HDRP(bp)+DSIZE // succ가 들어갈 주소
#define PRED(bp) *(char *)PRED_LOC(bp) // pred
#define SUCC(bp) *(char *)SUCC_LOC(bp)


static void *coalesce(void *);
static void *extend_heap(size_t);

static char *heap_listp;        // 힙 리스트의 시작 주소를 위한 포인터 변수 선언
void *root = NULL; // root 포인터 선언

/* 
 * mm_init - initialize the malloc package.
 * 힙 초기화
 */
int mm_init(void)
{
    /* Create the initial empty heap */                     // empty free list 만들기
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)   // 메모리 시스템에서 4 words를 가져와서 empty free list 초기화 (힙 시작 주소 초기화 and 힙 생성 후 크기를 4 words만큼 늘려주고 초기화)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)             // extend_heap 호출 -> 힙을 CHUNKSIZE 바이트로 확장, initial free block 생성(NULL 초기화)
        return -1;
    
    void *start = heap_listp + DSIZE;
    PUT(HDRP(start), PACK(CHUNKSIZE, 0));
    PUT(FTRP(start), PACK(CHUNKSIZE, 0));
    PUT(PRED_LOC(start), NULL);
    PUT(SUCC_LOC(start), heap_listp);
    root = SUCC_LOC(start);
    
    return 0;                                               // 할당기 초기화 완료, application으로부터 할당과 반환 요청 받을 준비 완료
}

/*
* extend_heap - Called by initializing heap or finding appropriate fit on mm_malloc function
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;    // required size by allocator
    char *new_bp = bp + WSIZE;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;           // 정렬 유지를 위해 요청 크기(size)를 인접 2 words의 배수(8 byte)로 반올림
    if ((long)(bp = mem_sbrk(size)) == 1)                               // 메모리 시스템에 추가 힙 공간 요청(by mem_sbrk 함수)
        return NULL;

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
* find_fit - Search of the implicit free list
*/
static void *find_fit(size_t asize)
{
    char *bp = root; // bp는 가장 첫번째 free 블록을 가리킨다.
    size_t size = GET_SIZE(HDRP(bp - WSIZE)); // 헤더의 사이즈와 할당 여부 저장
    
    while (size < asize) {
        if (SUCC(bp) == heap_listp) {
            return NULL;
        }
        bp = SUCC(bp);
        size = GET_SIZE(HDRP(bp - WSIZE));
    }
    return bp - WSIZE;
}

/*
* place - Place the requested block at the beginning of the free block, splitting only if the size of the remainder would equal or exceed the minimum block size
*/
static void place(void *bp, size_t asize)
{
    size_t origin_size = GET_SIZE(HDRP(bp));        // 할당 가능한 메모리 블록의 사이즈 저장
    if (origin_size - asize >= 3 * DSIZE) {         // 할당 가능한 블록에서 할당할 블록의 사이즈 차가 쿼드워드보다 크거나 같다면 안쓰는 부분을 가용상태로
        PUT(SUCC_LOC(PRED(bp)), SUCC(bp));
        PUT(PRED_LOC(SUCC(bp)), PRED(bp));
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(bp + asize), PACK(origin_size - asize, 0));
        mm_free(bp + asize);
        root += asize;
    }
    else {                                          // 안쓰는 블록을 쪼개봤자 필요가 없다면, 전부 할당한다.
        root = SUCC(bp);
        PUT(HDRP(bp), PACK(origin_size, 1));
        PUT(FTRP(bp), PACK(origin_size, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;           /* Adjusted block size */
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 3 * DSIZE;
    else
        asize = DSIZE * ((size + (2 * DSIZE) + (DSIZE - 1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);       // extend and try allocation once more
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // bp에 할당된 메모리 블록의 헤더에서 정보를 가져와 size 변수에 저장
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0)); // bp에 할당된 메모리 블록의 헤더 가용상태로 변경
    PUT(FTRP(bp), PACK(size, 0)); // bp에 할당된 메모리 블록의 풋터 가용상태로 변경
    PUT(PRED(bp), NULL);
    PUT(SUCC(bp), SUCC(root));
    root = SUCC_LOC(bp);
    coalesce(bp); // bp에 할당된 메모리 블록과 인접한 블록들을 병합하는 함수 호출
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;                                     // 재할당 받을 블록의 헤더 포인터
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);                               // 요청 가용 블록 할당하여 블록 헤더 포인터 재지정
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);   // old allocated block의 size
    if (size < copySize)            // requested size < old size
      copySize = size;              // old size <- requested size 갱신
    memcpy(newptr, oldptr, size);   // newptr에 oldptr의 값을 size 크기 만큼 복사
    mm_free(oldptr);                // old allocated block => free
    return newptr;
}