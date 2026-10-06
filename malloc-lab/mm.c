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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define WSIZE 4     /* bytes */
#define DSIZE 8     /* bytes */
#define CHUNKSIZE (1<<12)  /* 2^12 = 4096, 1kb = 1024 bytes -> 4kb */

#define MAX(x, y) ((x) > (y)? (x): (y))

#define PACK(size, alloc) ((size) | (alloc))

/* 4바이트로 읽고 씀(unsigned int) */
#define GET(p)  (*(unsigned int *)(p))      /* 해당 포인터에 들어있는 주소로 들어가 값을 가져옴 */
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)     /* GET으로 가져온 비트 정보에서 사이즈만(앞에 7비트) 가져옴 */
#define GET_ALLOC(p) (GET(p) & 0x1)    /* GET으로 가져온 비트 정보에서 allocated만(마지막 1비트) 가져옴 */

/* Header를 가리킴 */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
/* Footer를 가리킴 */  
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)     /* bp기준 offset이기 때문에 bp + 전체 블록 크기 - header + footer */

/* 다음 블록의 bp를 가리킴 */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))    /* bp - WSIZE = 현재 블록의 Header. 따라서 GET_SIZE(bp - WSIZE)=블록의 전체 크기 */   
/* 이전 블록의 bp를 가리킴 */
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   /* 이전 블록의 footer(bp - DSIZE)로 가 footer에서 이전 블록의 size를 가져와서 뺌 */


static char *heap_listp;
/* 헬퍼 함수 프로토타입 선언 (Function Prototypes) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 초기 블록 세팅 설정 (16비트) */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)  /* (void *)-1: 포인터 값이 -1. mem_sbrk는 void *를 반환하는 함수이기 떄문 */
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */     /* 0 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */       /* 8/1 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */       /* 8/1 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */       /* 0/1 */
    heap_listp += (2*WSIZE);    /* prologue의 footer를 가리킴 */

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * 힙데 사용할 공간이 부족할 떄 힙에 새로운 free block을 하나 추가해서 힙의 크기를 늘리는 함수
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* words가 홀수이면 +1을 해서 짝수로 만든다. 블록 크기를 8의 배수로 만들기 위함. */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    /* 
     * sbrk는 성공하면 char *(주소값)를 반환하고 실패하면 (Void *)-1를 반환.
     * 따라서 bp의 타입을 long으로 바꿔 -1인지 확인
     */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */    /* size | free */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */    /* size | free */ 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilouge header */  /* 다음 블록의 header = 이전 블록의 footer의 끝 = epilogue 시작점 */

    return coalesce(bp);
}

void mm_free(void *bp)
{
    /* header로부터 블록 사이즈를 가져옴 */
    size_t size = GET_SIZE(HDRP(bp));

    /* header의 allocated를 0(free)로 put */
    PUT(HDRP(bp), PACK(size, 0));
    /* footer의 allocated를 0(free)로 put */
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 현재 노드가 free일 때 앞 뒤 블록의 alloc를 확인해 free인 블록과 결합하는 함수 */
/* 블록이 결합되는 경우 겹쳐지는 기존 footer와 header에는 합쳐진 블록의 playload로 합쳐짐. 다만 들어있던 데이터는 그대로. */
static void *coalesce(void *bp)
{
    /* 이전 블록의 allocated */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    /* 다음 블록의 allocated */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* 블록의 크기 */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: 이전 블록, 다음 블록 둘다 alloc=1인 경우. 못합침 */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* Case 2: 이전 블록: alloc=1, 다음 블록: alloc=0 */
    else if (prev_alloc && !next_alloc) {
        /* 다음 블록의 헤더로 블록 사이즈를 가져와 현재 블록 사이즈에 더함 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /* 변한 사이즈 header, footer에 put */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* Case 3: 이전 블록: alloc=0, 다음 블록: alloc=1 */
    else if (!prev_alloc && next_alloc) {
        /* 이전 블록의 헤더로 블록 사이즈를 가져와 현재 블록 사이즈에 더함 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        /* bp를 이전 블록의 bp로 변경 */
        bp = PREV_BLKP(bp);
    }

    /* Case4: 이전 블록: alloc=0, 다음 블록: alloc=0 */
    else {
        /* 이전 블록, 다음 블록 사이즈를 현재 블록 사이즈에 + */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        /* bp를 이전 블록의 bp로 변경 */
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

/* 실제 필요한 블록 크기 계산 -> 빈 블록 찾기(find_fit) -> 있으면 place로 할당 ->  없으면 extend_hip()으로 확장 -> 확장된 공간에서 place() -> 사용자에게 playload 주소(bp) 반환 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    /* 할당할 사이즈 <= 8일 경우, 최소 단위 블록 ([4, 8, 4])으로 만들어줌 */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else    
        /* size + (DSIZE) = playload + header. DSIZE - 1을 더하고 나누고 곱하는건 가장 가까운 8의 배수로 만들기 위함 */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* extend_hip을 할 때 asize가 CHUNKSIZE(4096)보다 작으면 4096크기만큼 확장을 함. 확장할 크기가 너무 작으면 sbrk를 자주 호출해야하기 때문 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* first-fit */
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {     /* 현재 블록의 크기가 0보다 큰지 순회하며 확인. epilouge를 만나면 종료(0/1) */
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {        /* alloc=0이고 asize <= 블록크기인 블록을 찾으면 bp 리턴 */
            return bp;
        }
    }

    return NULL;
}

/* 블록을 할당하고, 블록을 통째로 사용하지 쪼개서 사용할지 판단 */
/* bp = 할당 대상으로 선택된 블록의 playload 시작 주소, asize = 그 free block에 할당할 전체 블록 크기 */
static void place(void *bp, size_t asize)
{   
    /* 할당 대상(발견한)블록의 크기 */
    size_t csize = GET_SIZE(HDRP(bp));

    /* 할당하고 남는 공간 >= 16(최소 블록 크기)
     * O -> 쪼개기 가능
     * X -> 쪼개기 불가능
     */
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        /* 남는 공간 쪼개기 */
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t oldsize;
    size_t copySize;

    /* ptr == NULL이면 malloc과 동일 */
    if (ptr == NULL)
        return mm_malloc(size);

    /* size == 0이면 기존 블록 해제 */
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* 기존 블록의 전체 크기 */
    oldsize = GET_SIZE(HDRP(ptr));

    /* 기존 payload 크기 = 전체 블록 크기 - header - footer */
    copySize = oldsize - 2 * WSIZE;

    /* 새 크기보다 기존 payload가 크면 새 크기만 복사 */
    if (size < copySize)
        copySize = size;

    /* 새로운 블록 할당 */
    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    /* 기존 데이터 복사 */
    memcpy(newptr, ptr, copySize);

    /* 기존 블록 해제 */
    mm_free(ptr);

    return newptr;
}














