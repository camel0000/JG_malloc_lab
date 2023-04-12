/*
* Explicit_malloc_lab
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "1team",
    /* First member's full name */
    "MinkiCho",
    /* First member's email address */
    "camel0000@naver.com",
    /* Second member's full name (leave blank if none) */
    "SeongbeomAhn",
    /* Second member's email address (leave blank if none) */
    "HaejeongLim"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */       // word 사이즈
#define DSIZE 8             /* Double word size (bytes) */                  // double word 사이즈
#define CHUNKSIZE (1 << 12)   /* Extend heap by this amount (bytes) */      // 초기 free block과 heap extension을 위한 기본 크기 CHUNKSIZE

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)                     // 주소 조정을 위한(?) 조정할 사이즈 정의(?)

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

#define PRED_LOC(bp) (HDRP(bp) + WSIZE)                                     // prev가 들어갈 주소
#define SUCC_LOC(bp) (HDRP(bp) + DSIZE)                                     // succ가 들어갈 주소
#define PREV_PRED(bp) (GET(PRED_LOC(bp)))                                   // *(char *)PRED_LOC(bp)
#define NEXT_SUCC(bp) (GET(SUCC_LOC(bp)))                                   // *(char *)SUCC_LOC(bp)


static void *free_coalesce(void *bp, void *pred, void *succ);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp;    // 프롤로그 footer 블록
void *root = NULL;          // 첫 가용 블록의 successor 가리키는 포인터

/* 
 * mm_init - initialize the malloc package.
 * 힙 초기화
 */
int mm_init(void)
{
    /* Create the initial empty heap */ 
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }

    void *start = heap_listp + DSIZE;       // 첫번째 가용 블록의 헤더
    PUT(HDRP(start), PACK(CHUNKSIZE, 0));
    PUT(FTRP(start), PACK(CHUNKSIZE, 0));
    PUT(PRED_LOC(start), heap_listp-WSIZE);
    PUT(SUCC_LOC(start), heap_listp);
    root = SUCC_LOC(start);
    return 0;
}

/*
* extend_heap - Called by initializing heap or finding appropriate fit on mm_malloc function
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;    // required size by allocator

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free blcok footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
* find_fit - Search of the implicit free list
* 할당 예정 메모리 size에 맞는 블록 찾기
*/
static void *find_fit(size_t asize)
{
    char *succ = root;                          // 가장 첫 가용 블록의 다음 블록을 가리키기 위한 succ 포인터
    size_t size = GET_SIZE(HDRP(succ - WSIZE));

    // 가용 블록 size가 할당 예정 블록의 size보다 작을 경우
    while (size < asize) {
        // 해당 블록에서 다음으로 heap_listp를 가리키는 경우(== 마지막 블록인 경우 == 탐색을 다 했으나, 적절한 가용 블록을 찾지 못한 경우)
        if (NEXT_SUCC(succ - WSIZE) == heap_listp) {    
            return NULL;
        }
        succ = NEXT_SUCC(succ - WSIZE);         // 헤더와 사이즈를 갱신
        size = GET_SIZE(HDRP(succ - WSIZE));
    }
    return succ - WSIZE;
}

/*
* place - Place the requested block at the beginning of the free block, splitting only if the size of the remainder would equal or exceed the minimum block size
* 요청 받은 메모리를 적절한 위치의 가용 블록에 할당
*/
static void place(void *bp, size_t asize)
{
    size_t origin_size = GET_SIZE(HDRP(bp));    // 할당 가능한 메모리 블록의 본래 사이즈 저장
    char *new_bp = bp + asize;                  // 부분 할당 후 남은 가용 블록의 헤더
    char *ex_bp = bp + origin_size;             // extend한 가용 블록의 헤더
    
    // 할당 가능 블록 - 할당 예정 블록의 size 차이가 24bytes보다 크거나 같을 경우 -> 해당 블록 할당 / 가용 분리
    if (origin_size - asize >= 3 * DSIZE) {
        // 블록 하나, 부분 할당
        if (PREV_PRED(bp) == heap_listp - WSIZE && NEXT_SUCC(bp) == heap_listp) {
            PUT(PRED_LOC(new_bp), heap_listp - WSIZE);
            PUT(SUCC_LOC(new_bp), heap_listp);
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
            PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
            root = SUCC_LOC(new_bp);
        }
        // 가용 블록 두 개 이상, 부분 할당
        else {
            // 마지막 블록, 부분 할당
            if (NEXT_SUCC(bp) == heap_listp) {
                PUT(SUCC_LOC(new_bp), root);
                PUT(PRED_LOC(new_bp), PREV_PRED(root - WSIZE));
                PUT(SUCC_LOC(PREV_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(root - WSIZE), PRED_LOC(new_bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
            // 첫 블록, 부분 할당
            else if (PREV_PRED(bp) == heap_listp - WSIZE) {
                PUT(SUCC_LOC(new_bp), NEXT_SUCC(bp));
                PUT(PRED_LOC(new_bp), PREV_PRED(bp));
                PUT(NEXT_SUCC(bp) - WSIZE, PRED_LOC(new_bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
            // 중간 블록, 부분 할당
            else {
                PUT(SUCC_LOC(new_bp), root);
                PUT(PRED_LOC(root - WSIZE), PRED_LOC(new_bp));
                PUT(PRED_LOC(new_bp), PREV_PRED(root - WSIZE));
                PUT(SUCC_LOC(PREV_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(NEXT_SUCC(bp) - WSIZE), PREV_PRED(bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
        }
    }
    // 부분 할당 불가능 -> 전체 할당
    else {
        // 할당 가능 블록 하나, 전체 할당
        if (NEXT_SUCC(bp) == heap_listp && PREV_PRED(bp) == heap_listp - WSIZE) {
            PUT(HDRP(bp), PACK(origin_size, 1));
            PUT(FTRP(bp), PACK(origin_size, 1)); 
            ex_bp = extend_heap(CHUNKSIZE / WSIZE);
            PUT(PRED_LOC(ex_bp), heap_listp - WSIZE);
            PUT(SUCC_LOC(ex_bp), heap_listp);
            root = SUCC_LOC(ex_bp);
        }
        
        // 블록 여러개 전부 할당
        else {
            // 마지막 블록, 전체 할당
            if (NEXT_SUCC(bp) == heap_listp) { 
                PUT(SUCC_LOC(PREV_PRED(bp)), NEXT_SUCC(bp));
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));  
                ex_bp = extend_heap(CHUNKSIZE / WSIZE);
                PUT(PRED_LOC(ex_bp), PREV_PRED(root - WSIZE));
                PUT(SUCC_LOC(ex_bp), root);
                PUT(PRED_LOC(root - WSIZE), PRED_LOC(ex_bp));
                root = SUCC_LOC(ex_bp);
            }
            // 첫 블록, 전체 할당
            else if (PREV_PRED(bp) == heap_listp-WSIZE) {
                PUT(PRED_LOC(NEXT_SUCC(bp) - WSIZE), PREV_PRED(bp));
                root = NEXT_SUCC(bp);
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));  
            }
            // 중간 블록, 전체 할당
            else {
                PUT(SUCC_LOC(PREV_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(NEXT_SUCC(bp) - WSIZE), PREV_PRED(bp));
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));
            }
        }
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
        asize = 3 * DSIZE;                                              // 요청 메모리가 더블워드보다 작으면 24bytes로 설정
    else
        asize = DSIZE * ((size + (2 * DSIZE) + (DSIZE - 1)) / DSIZE);   // 그 외에는 요청한 메모리 크기에 헤더와 풋터의 오버헤드를 고려해서 크기 설정

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
* coalesce - Coalescing with boundary tags the adjacent blocks
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // 이전 블록 할당, 다음 블록 할당
    if (prev_alloc && next_alloc) {
        return bp;
    }
    // 이전 블록 할당, 다음 블록 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0)); 
    }
    // 이전 블록 가용, 다음 블록 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // 이전 블록 가용, 다음 블록 가용
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0)); 
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
* free_coalesce - Coalescing with boundary tags the adjacent blocks and saving the 'root' imfo in mm_free
*/
static void *free_coalesce(void *bp, void *pred, void *succ)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록 할당, 다음 블록 할당
    if (prev_alloc && next_alloc) {
        return bp;
    }
    // 이전 블록 할당, 다음 블록 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        pred = GET((NEXT_BLKP(bp)));              // 다음 블록의 prd
        succ = GET((NEXT_BLKP(bp) + WSIZE));      // 다음 블록의 succ
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    // 이전 블록 가용, 다음 블록 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        pred = GET((PREV_BLKP(bp)));              // 이전 블록의 prd
        succ = GET((PREV_BLKP(bp) + WSIZE));      // 이전 블록의 succ
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // 이전 블록 가용, 다음 블록 가용
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        pred = GET((PREV_BLKP(bp)));              // 이전 블록의 pred
        succ = GET((NEXT_BLKP(bp) + WSIZE));      // 다음 블록의 succ
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_free - Freeing a block does nothing
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    char *pred;                                     // coalescing될 블록의 pred가 가리키는 주소
    char *succ;                                     // coalescing될 블록의 succ가 가리키는 주소
    char *origin_root_pred = PRED_LOC(root-WSIZE);  // 본래 root의 pred 주소
    char *origin_root_succ = SUCC_LOC(root-WSIZE);  // 본래 root의 succ 주소
    bp = free_coalesce(bp, pred, succ);
    root = SUCC_LOC(bp);                            // coalescing되고 갱신된 bp로 root 갱신

    // coalescing된 후에도 가용 블록 1개일 경우
    if(NEXT_SUCC(origin_root_pred) == heap_listp) {
        PUT(SUCC_LOC(bp), heap_listp);
        PUT(PRED_LOC(bp), heap_listp - WSIZE);
    }
    // coalescing된 후에 새로운 블록이 생긴 경우
    else {
        // coalescing 되기 전, 앞 뒤 블록 연결
        PUT(SUCC_LOC(pred), succ);
        PUT(PRED_LOC(succ-WSIZE), pred);
        PUT(SUCC_LOC(bp), origin_root_succ);        // bp succ에 본래 root PUT
        PUT(origin_root_pred, PRED_LOC(bp));        // 본래 root pred가 새로운 블록 pred pointing
        PUT(PRED_LOC(bp), heap_listp-WSIZE);
    }
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
    if (size < copySize)                                    // requested size < old size
      copySize = size;                                      // old size <- requested size 갱신
    memcpy(newptr, oldptr, size);                           // newptr에 oldptr의 값을 size 크기 만큼 복사
    mm_free(oldptr);                                        // old allocated block => free
    return newptr;
}