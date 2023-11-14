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
    "101호_1팀", "김주영","juyeong.kim.201@gmail.com", "", ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의 */
#define WSIZE 4 /* Word and head/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes)*/
/* 1을 12bit 왼쪽으로 shift. 즉, CHUNKSIZE = 2^12 = 4096 bytes
많은 시스템에서 페이지 크기는 4kb. 힙 확장은 일반적으로 페이지 크기의 배수로 확장함. */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

#define PACK(size, alloc) ((size) | (alloc))        /* 헤더에 넣을 정보 생성 (만약 size=16byte, 할당되었다면 PACK(16,1) = 17) */ 
#define GET(p) (*(unsigned int *)(p))               /* 주소 p에 접근하여 워드를 read, write */
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)                 /* 주소 p에 접근하여 size, allocated fields 읽기. ~는 비트 뒤집어주는 문법 */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 
bp(block ptr)가 주어지면 header, footer의 주소를 계산 
(bp를 char 타입으로 캐스팅하는 이유는 1 byte 단위로 계산하기 위해서)
*/
#define HDRP(bp) ((char *)(bp) - WSIZE) // HeaDeR Pointer
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // FooTeR Pointer

/* bp(block ptr)가 주어지면, 이전 블록과 이후 블록의 시작 주소를 계산 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) // BLocK Pointer
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);

/* heap_listp는 프롤로그 블록 바로 다음에 위치하는 첫 번째 가용 블록을 가리킨다. 
init된 직후에는 heap의 시작 부분을 가리킨다. */
static void *heap_listp; 

static void *prev_bp;

/* mm_init creates a heap with an initial free block */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }

    PUT(heap_listp, 0); /* 정렬 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* 에필로그 header */
    heap_listp += (2*WSIZE);

    // prev_bp = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    
    return 0;
}


/* extend_heap() extends the heap with a new free block */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* 정렬을 유지하기 위해 짝수 개의 워드를 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* mm_malloc - brk 포인터를 증가시켜 블록을 할당.
항상 크기가 alignment의 배수인 블록을 할당한다. */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* fake 요청은 무시 */
    if(size == 0){
        return NULL;
    }

    /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정 */
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* 적합한 free list 탐색 */
    if ((bp = find_fit(asize)) != NULL ){
        place(bp, asize); // 찾은 위치에 asize 만큼 메모리 배치
        return bp;
    }

    /* No fit found. 추가 메모리 할당 및 블록 배치 */

    // extendsize = MAX(asize, CHUNKSIZE);
    extendsize = asize;
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}


// static void *find_fit(size_t asize)
// {
//     /* First-fit search */
//     void *bp;
//     // 에필로그 헤더를 만날 때까지 옆 블록으로 이동하면서 순회
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         // 할당되지 않았고, asize보다 크다면
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ 
//             return bp;
//         }
//     }
//     return NULL; /* No fit */
// } 

/* next fit */
static void *find_fit(size_t asize)
{
    void *bp;

    // HDRP(PREV_BLKP(bp))
    
    /* prev_bp 부터 에필로그 헤더까지 탐색 */
    for (bp = prev_bp; GET_SIZE(HDRP(prev_bp)) > 0; bp = NEXT_BLKP(bp)){
        /* 할당되지 않았고, asize보다 크다면 */
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ 
            prev_bp = bp;
            return bp;
        }
    }

    /* 처음부터 prev_bp까지 탐색 */
    for (bp = heap_listp; bp < prev_bp; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            prev_bp = bp;
            return bp;
        }
    }

    return NULL; /* No fit */
}

// 분할 전략: 필요한 만큼만 할당하고 남은 부분은 가용 블록으로 분할
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 해당 공간의 사이즈 탐색

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1)); // 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 필요한 부분을 제외한 나머지는 free로 분리
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));        
    }
}


/* free 연산 + 즉시 연결 전략 */ 
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp); // 즉시 연결
}


static void *coalesce(void *bp)
{
    // GET_ALLOC: 해당 주소의 마지막 비트 반환 -> 헤더 or 푸터라면, 할당됐으면 1, 아니면 0 반환됨
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 푸터 접근 -> 할당여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더 접근 -> 할당여부 확인
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

    // if문에서 0은 false, 그 외 숫자는 true로 인식
    if (prev_alloc && next_alloc){              /* Case 1. 이전 & 다음 not free */
        return bp;
    } 
    else if (prev_alloc && !next_alloc){        /* Case 2. 다음 블록 free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){        /* Case 3. 이전 블록 free */
        void *old_bp = bp;

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        if (old_bp == prev_bp){ // next-fit 시작 지점일 경우 처리
            prev_bp = bp;
        }
    }
    else {                                      /* Case 4. 이전 & 다음 free */
        void *old_bp = bp;
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        if (old_bp == prev_bp){ // next-fit 시작 지점일 경우 처리
            prev_bp = bp;
        }
    }
    return bp;
}


/*
 * mm_realloc - mm_malloc 및 mm_free을 통해 간단하게 구현됨
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}






