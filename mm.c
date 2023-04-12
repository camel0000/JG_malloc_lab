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

#define WSIZE 4 // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8 // 더블우드 사이즈(bytes)
#define CHUNKSIZE (1<<12) // heap을 이만큰 늘리겠다(bytes) = 2의12승

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // size와 alloc인자를 or 비트연산한다.

#define GET(p) (*(unsigned int *)(p)) // p가 가리키는 주소의 값을 가져온다
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 주소에 val을 넣는다

#define GET_SIZE(p) (GET(p) & ~0x7) // and 연산으로 주소 p에 있는 사이즈를 얻는다. 하위 3비트를 제외한 값을 읽는다.
#define GET_ALLOC(p) (GET(p) & 0x1) // GET(p)의 가장 오른쪽 비트를 추출한다. 비트가 1이면 할당상태 0이면 가용상태

#define HDRP(bp) ((char *)(bp) - WSIZE) // 헤더 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터 반환

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록 포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록 포인터 반환

#define PRED_LOC(bp) (HDRP(bp)+WSIZE) // prev가 들어갈 주소
#define SUCC_LOC(bp) (HDRP(bp)+DSIZE) // succ가 들어갈 주소
#define POST_PRED(bp) (GET(PRED_LOC(bp)))// pred
#define NEXT_SUCC(bp) (GET(SUCC_LOC(bp)))//  *(char *)SUCC_LOC(bp)


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 사이즈가 8의 배수로 정렬된 값이 된다.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *free_coalesce(void *bp, void *pred, void *succ);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

// 프롤로그 블록
static char *heap_listp;
//최초 가용 블록으로 힙 생성하기
void *root = NULL; // root 포인터 선언

int mm_init(void)
{
    // mem_sbrk: 힙 영역을 incr bytes만큼 확장, 새로 할당된 힙 영역의 첫번째 byte를 가리키는 포인터 리턴
    // 불러올 수 없으면 -1 반환
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0); // 패딩 할당
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue 헤더 생성
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue 풋터 생성
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // epilogue 헤더 생성
    heap_listp += (2 * WSIZE); // heap_listp을 더블워드만큼 증가시켜 할당 가능한 메모리 블록의 시작 주소를 가리키도록 함

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    void *start = heap_listp + DSIZE; // pred_loc
    PUT(HDRP(start), PACK(CHUNKSIZE, 0));
    PUT(FTRP(start), PACK(CHUNKSIZE, 0));
    PUT(PRED_LOC(start), heap_listp-WSIZE); // heap_listp-WSIZE가 제대로 안들어가고 있음
    PUT(SUCC_LOC(start), heap_listp);
    root = SUCC_LOC(start);
    // printf("--------------------init----------------------\n");
    return 0;
}
// 새 가용 블록으로 힙 확장하기
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 요청한 크기를 2워드의 배수로 반올림하고 추가 힙 공간 요청
    // words가 홀수라면 반올림하고 추가 힙 공간 요청
    size = (words%2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0)); // size만큼 가용블록 생성
    PUT(FTRP(bp), PACK(size, 0)); 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그의 헤더가 된다.
    
    return coalesce(bp);
}

// 할당하려고 하는 메모리가 들어갈 수 있는 블록 찾기
static void *find_fit(size_t asize)
{   // asize == 할당할 메모리 사이즈
    char *bp = root; // bp는 가장 첫번째 free 블록을 가리킨다.
    size_t size = GET_SIZE(HDRP(bp - WSIZE)); // 헤더의 사이즈와 할당 여부 저장

    // for(bp = root; GET_ALLOC(HDRP(bp - WSIZE)) != 1; bp = NEXT_SUCC(bp - WSIZE)) {
    //     if (asize <= GET_SIZE(HDRP(bp - WSIZE))) {
    //         return bp - WSIZE;
    //     }
    // }
    // return NULL;
    
    while (size < asize) {
        if (NEXT_SUCC(bp - WSIZE) == heap_listp) {
            return NULL;
        }
        // printf("while!\n");
        bp = NEXT_SUCC(bp - WSIZE);
        size = GET_SIZE(HDRP(bp - WSIZE));
    }
    // printf("no while\n");
    return bp - WSIZE;
}

static void place(void *bp, size_t asize)
{
    size_t origin_size = GET_SIZE(HDRP(bp)); // 할당 가능한 메모리 블록의 사이즈 저장
    char *new_bp = bp + asize;
    char *ex_bp = bp + origin_size;
    
    if (origin_size - asize >= 3 * DSIZE) { // 할당 가능한 블록에서 할당할 블록의 사이즈 차가 쿼드워드보다 크거나 같다면 안쓰는 부분을 가용상태로
        if (POST_PRED(bp) == heap_listp-WSIZE && NEXT_SUCC(bp) == heap_listp) { // 블록 하나, 부분 할당
            // printf("only one divided free\n");
            PUT(PRED_LOC(new_bp), heap_listp-WSIZE);
            PUT(SUCC_LOC(new_bp), heap_listp);
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
            PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
            root = SUCC_LOC(new_bp);
        }
        else{
            if(NEXT_SUCC(bp) == heap_listp) // 마지막 블록 부분할당
            {
                // printf("last brk divide\n");
                PUT(SUCC_LOC(new_bp), root);
                PUT(PRED_LOC(new_bp), POST_PRED(root-WSIZE)); // POST_PRED(root-WSIZE) == heap_listp-wsize
                PUT(SUCC_LOC(POST_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(root-WSIZE), PRED_LOC(new_bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
            else if(POST_PRED(bp) == heap_listp-WSIZE) // 첫 블록 부분할당
            {
                // printf("first brk divide\n");
                PUT(SUCC_LOC(new_bp), NEXT_SUCC(bp));
                PUT(PRED_LOC(new_bp), POST_PRED(bp)); // POST_PRED(root-WSIZE) == heap_listp-wsize
                PUT(NEXT_SUCC(bp) - WSIZE, PRED_LOC(new_bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
            else // 중간블록 부분할당
            {
                // printf("middle brk divide\n");
                PUT(SUCC_LOC(new_bp), root);
                PUT(PRED_LOC(root-WSIZE), PRED_LOC(new_bp));
                PUT(PRED_LOC(new_bp), POST_PRED(root-WSIZE)); // POST_PRED(root-WSIZE) == heap_listp-wsize
                PUT(SUCC_LOC(POST_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(NEXT_SUCC(bp)-WSIZE), POST_PRED(bp));
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                PUT(HDRP(new_bp), PACK(origin_size - asize, 0));
                PUT(FTRP(new_bp), PACK(origin_size - asize, 0));
                root = SUCC_LOC(new_bp);
            }
        }
    }
    else { // 안쓰는 블록을 쪼개봤자 필요가 없다면, 전부 할당한다.
        if(NEXT_SUCC(bp) == heap_listp && POST_PRED(bp) == heap_listp-WSIZE) // free블록 하나이면서 전부 할당
        {
            // printf("only one all free\n");
            PUT(HDRP(bp), PACK(origin_size, 1));
            PUT(FTRP(bp), PACK(origin_size, 1)); 
            ex_bp = extend_heap(CHUNKSIZE/WSIZE);
            PUT(PRED_LOC(ex_bp), heap_listp-WSIZE); //POST_PRED(bp) == heap_listp-wsize
            PUT(SUCC_LOC(ex_bp), heap_listp);
            root = SUCC_LOC(ex_bp);
        }
        else{ // 블록 여러개 전부 할당
            if (NEXT_SUCC(bp) == heap_listp)
            { // 마지막 블록 전체 할당
                // printf("last brk all free\n");
                PUT(SUCC_LOC(POST_PRED(bp)), NEXT_SUCC(bp)); // 할당된 블록 양옆 연결
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));  
                ex_bp = extend_heap(CHUNKSIZE/WSIZE);
                PUT(PRED_LOC(ex_bp), POST_PRED(root-WSIZE));  // ex_bp의 pred는 원래 root의 pred값을 가진다.
                PUT(SUCC_LOC(ex_bp), root); // ex_bp의 suc은 root를 가진다. 
                PUT(PRED_LOC(root-WSIZE), PRED_LOC(ex_bp)); //PUT(SUCC_LOC(POST_PRED(ex_bp)), heap_listp);               
                root = SUCC_LOC(ex_bp);
            }
            else if(POST_PRED(bp) == heap_listp-WSIZE) // 첫번째 블록 전체 할당
            {
                // printf("first brk all free\n");
                PUT(PRED_LOC(NEXT_SUCC(bp)-WSIZE), POST_PRED(bp));
                root = NEXT_SUCC(bp); // next_succ(bp)를 쓰려면 할당되기 전에 안그러면 정보 사라짐
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));  
            }
            else{ // 중간 블록 전체 할당
                // printf("middle brk all free\n");
                PUT(SUCC_LOC(POST_PRED(bp)), NEXT_SUCC(bp));
                PUT(PRED_LOC(NEXT_SUCC(bp)-WSIZE), POST_PRED(bp));
                PUT(HDRP(bp), PACK(origin_size, 1));
                PUT(FTRP(bp), PACK(origin_size, 1));
            }
        }
    }
}

// 가용 리스트에서 블록 할당하기
void *mm_malloc(size_t size)
{
    size_t asize; // 할당할 메모리 블록의 크기 저장 변수
    size_t extendsize; // 확장할 메모리 블록의 크기 저장 변수
    char *bp;

    if (size == 0){ // 요청한 메모리 크기가 0인 경우
        return NULL;
    }

    // 요청한 메모리 블록의 크기를 바탕으로 실제 할당할 메모리 크기 계산
    if (size <= DSIZE){ // 요청 메모리가 더블워드보다 작으면 쿼드 워드로 설정
        asize = 3 * DSIZE;
    }else{ // 그 외에는 요청한 메모리 크기에 헤더와 풋터의 오버헤드를 고려해서 크기 설정
        asize = DSIZE * ((size + (2 * DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 가용 블록을 가용리스트에서 검색하고 할당기는 요청한 블록을 배치한다.
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    //맞는 블록을 찾기 못한다면 새로운 가용 블록으로 확장하고 배치한다.
    extendsize = MAX(asize, CHUNKSIZE);
    // 힙 영역이 부족해서 늘릴 수 없을 때
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize); // 다시 메모리 할당하기

    return bp;
}

// 경계 태그 연결을 사용해서 상수 시간에 인접 가용 블록들과 통합한다.
static void *coalesce(void *bp) // 수정 필요
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 헤더에서 할당 정보 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 할당 정보 저장
    size_t size = GET_SIZE(HDRP(bp)); // bp의 헤더에서 사이즈 정보 저장
    // case 1: 이전, 다음 블록 모두 할당된 상태면 bp 반환
    if (prev_alloc && next_alloc){
        return bp;
    }
    // case 2: 이전 블록 할당, 다음 블록 가용 상태라면
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 사이즈 정보를 가져와 size에 저장
        PUT(HDRP(bp), PACK(size,0)); // bp의 헤더와 풋터의 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(FTRP(bp), PACK(size,0)); 
    }
    // case 3: 이전 블록 가용, 다음 블록 할당 상태라면
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 헤더에서 사이즈 정보를 가져와 size에 저장
        PUT(FTRP(bp), PACK(size,0)); // bp의 풋터 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 이전 블록의 헤더 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        bp = PREV_BLKP(bp); //bp를 이전 블록으로 옮겨줌
    }
    // case 4: 양쪽 블록 모두 가용 상태라면
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 양쪽 블로의 헤더에 저장된 사이즈 정보를 더해 size에 저장
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 양쪽 블록의 헤더와 풋터 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0)); 
        bp = PREV_BLKP(bp); //bp를 이전 블록으로 옮겨줌
    }
    return bp;
}

static void *free_coalesce(void *bp, void *pred, void *succ) // 수정 필요
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 헤더에서 할당 정보 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 할당 정보 저장
    size_t size = GET_SIZE(HDRP(bp)); // bp의 헤더에서 사이즈 정보 저장
    // case 1: 이전, 다음 블록 모두 할당된 상태면 bp 반환
    if (prev_alloc && next_alloc){
        return bp;
    }
    // case 2: 이전 블록 할당, 다음 블록 가용 상태라면
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 사이즈 정보를 가져와 size에 저장
        pred = GET((NEXT_BLKP(bp))); // 다음 블록의 prd
        succ = GET((NEXT_BLKP(bp)+WSIZE)); // 다음 블록의 succ
        PUT(HDRP(bp), PACK(size,0)); // bp의 헤더와 풋터의 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(FTRP(bp), PACK(size,0));
    }
    // case 3: 이전 블록 가용, 다음 블록 할당 상태라면
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 헤더에서 사이즈 정보를 가져와 size에 저장
        pred = GET((PREV_BLKP(bp))); // 이전 블록의 prd
        succ = GET((PREV_BLKP(bp)+WSIZE)); // 이전 블록의 succ
        PUT(FTRP(bp), PACK(size,0)); // bp의 풋터 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 이전 블록의 헤더 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        bp = PREV_BLKP(bp); //bp를 이전 블록으로 옮겨줌
    }
    // case 4: 양쪽 블록 모두 가용 상태라면
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 양쪽 블로의 헤더에 저장된 사이즈 정보를 더해 size에 저장
        pred = GET((PREV_BLKP(bp))); // 이전 블록의 pred
        succ = GET((NEXT_BLKP(bp)+WSIZE)); // 다음 블록의 succ
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 양쪽 블록의 헤더와 풋터 사이즈를 통합한 사이즈로 변경, 가용상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp); //bp를 이전 블록으로 옮겨줌
    }
    return bp;
}

// 블록을 반환
void mm_free(void *bp)
{
    // bp에 할당된 메모리 블록의 헤더에서 정보를 가져와 size 변수에 저장
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0)); // bp에 할당된 메모리 블록의 헤더 가용상태로 변경
    PUT(FTRP(bp), PACK(size, 0)); // bp에 할당된 메모리 블록의 풋터 가용상태로 변경
    char *pred; // coal될 블록의 pred 안의 값
    char *succ; // coal될 블록의 succ 안의 값
    char *origin_root_pred = PRED_LOC(root-WSIZE); //원래 root의 pred
    char *origin_root_succ = SUCC_LOC(root-WSIZE); //원래 root의 succ
    bp = free_coalesce(bp, pred, succ);
    root = SUCC_LOC(bp); // coal되고 갱신된 bp로 root 갱신

    if(NEXT_SUCC(origin_root_pred) == heap_listp) // coal된 후에도 free 블록 1개
    {
        PUT(SUCC_LOC(bp), heap_listp);
        PUT(PRED_LOC(bp), heap_listp - WSIZE); //POST_PRED(root-WSIZE) = heap_list - WSIZE
        // root = SUCC_LOC(bp);
    }
    else if(GET_ALLOC(NEXT_BLKP(bp)) == 1 && GET_ALLOC(PREV_BLKP(bp)) == 1)
    {
        PUT(SUCC_LOC(bp), origin_root_succ); // bp succ에 원래 root 넣기
        PUT(origin_root_pred, PRED_LOC(bp)); // 원래 root pred가 새로운 블록 pred 가리키기
        PUT(PRED_LOC(bp), heap_listp-WSIZE); // POST_PRED(root-WSIZE) == heap_listp-wsize
    }
    else // coal된 후에 새로운 블록이 생김
    {
        // coal되기 전에 앞 뒤 블록 연결
        PUT(SUCC_LOC(pred), succ);
        PUT(PRED_LOC(succ-WSIZE), pred);
        PUT(SUCC_LOC(bp), origin_root_succ); // bp succ에 원래 root 넣기
        PUT(origin_root_pred, PRED_LOC(bp)); // 원래 root pred가 새로운 블록 pred 가리키기
        PUT(PRED_LOC(bp), heap_listp-WSIZE); // POST_PRED(root-WSIZE) == heap_listp-wsize
        // root = SUCC_LOC(bp);
    }
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 기존 메모리 블록의 포인터
    void *newptr; // 새롭게 늘리고 싶은 메모리 블록의 포인터
    size_t copySize; // 원본 메모리 블록 크기 저장
    
    newptr = mm_malloc(size); // 새롭게 늘리고 싶은 메모리 size만큼 동적 할당하고, 그 주소 저장
    if (newptr == NULL) // newptr이 NULL일 때가 언제지?
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); // oldptr이 가리키는 블록의 시작 주소에서 8바이트 뒤에 있는 즉, 헤더에 있는 사이즈 저장
    if (size < copySize) // 늘리고싶은 메모리 크기가 원본의 메모리 크기보다 작다면 
      copySize = size; // 원본의 메모리 크기를 size로 바꿔서 메모리 낭비를 줄인다.
    memcpy(newptr, oldptr, size); // oldptr이 가리키는 메모리 블록에서 copysize만큼 데이터를 newptr이 가리키는 메모리 블록으로 복사
    mm_free(oldptr);
    return newptr;
}