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
/* free block이 부족하면 heap을 얼마나 확장할지 */
#define CHUNKSIZE (1<<12)  /* 2^12 = 4096, 1kb = 1024 bytes -> 4kb */

/* 분리 가용 리스트 개수 */
#define LIST_NUM 10

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
#define GET_PTR(p)       (*(void **)(p))
#define PUT_PTR(p, val)  (*(void **)(p) = (val))

#define SUCC(bp) (*(void **)((char *)(bp)))


static char *heap_listp;
static void *seg_free_lists[LIST_NUM];
/* 헬퍼 함수 프로토타입 선언 (Function Prototypes) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_free_block(void *bp);
int get_list_index(size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void *bp;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);

    for (int i = 0; i < LIST_NUM; i++)
        seg_free_lists[i] = NULL;

    if ((bp = extend_heap(CHUNKSIZE / WSIZE)) == NULL)
        return -1;

    return 0;
}

/* 
 * 분리 가용 리스트-분리맞춤
 * header, footer 필요
 * free list 필요
 *  free list는 크기 클래스별로 나눠져있음.
 *  free하거나 split을 해서 생긴 free block을 해당 크기 클래스의 free list의 맨 앞에 넣는 LIFO 방식.
 * 
*/

static void insert_free_block(void *bp)
{
    int index = get_list_index(GET_SIZE(HDRP(bp)));

    SUCC(bp) = seg_free_lists[index];
    seg_free_lists[index] = bp;
}


/* size class 결정 */
int get_list_index(size_t size)
{
    if (size <= 31)     return 0;
    if (size <= 63)     return 1;
    if (size <= 127)    return 2;
    if (size <= 255)    return 3;
    if (size <= 511)    return 4;
    if (size <= 1023)   return 5;
    if (size <= 2047)   return 6;
    if (size <= 4095)   return 7;
    if (size <= 8191)   return 8;
    else                return 9;
}


/* 
 * heap에 새로운 공간을 확보해서 free block을 만드는 함수
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2)
        ? (words + 1) * WSIZE
        : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    bp = coalesce(bp);

    insert_free_block(bp);

    return bp;
}

static void remove_free_block(void *bp)
{
    int index = get_list_index(GET_SIZE(HDRP(bp)));

    void *current = seg_free_lists[index];
    void *prev = NULL;

    while (current != NULL)
    {
        if (current == bp)
        {
            if (prev == NULL)
            {
                // bp가 리스트의 첫 번째 노드
                seg_free_lists[index] = SUCC(current);
            }
            else
            {
                // 이전 노드가 bp를 건너뛰도록 연결
                SUCC(prev) = SUCC(current);
            }

            SUCC(current) = NULL;
            return;
        }

        prev = current;
        current = SUCC(current);
    }
}


void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    bp = coalesce(bp);

    insert_free_block(bp);
}

/* 현재 노드가 free일 때 앞 뒤 블록의 alloc를 확인해 free인 블록과 결합하는 함수 */
/* 블록이 결합되는 경우 겹쳐지는 기존 footer와 header에는 합쳐진 블록의 playload로 합쳐짐. 다만 들어있던 데이터는 그대로. */
static void *coalesce(void *bp)
{
    size_t prev_alloc =
        GET_ALLOC(FTRP(PREV_BLKP(bp)));

    size_t next_alloc =
        GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size =
        GET_SIZE(HDRP(bp));

    /* Case 1 */
    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    /* Case 2: 다음 블록과 합침 */
    else if (prev_alloc && !next_alloc)
    {
        remove_free_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* Case 3: 이전 블록과 합침 */
    else if (!prev_alloc && next_alloc)
    {
        remove_free_block(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    /* Case 4: 이전 + 다음 둘 다 합침 */
    else
    {
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

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

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE *
                ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}

/* segregated-fit */
static void *find_fit(size_t asize)
{
    int index = get_list_index(asize);

    for (int i = index; i < LIST_NUM; i++)
    {
        void *bp = seg_free_lists[i];

        while (bp != NULL)
        {
            if (GET_SIZE(HDRP(bp)) >= asize)
                return bp;

            bp = SUCC(bp);
        }
    }

    return NULL;
}

/* 블록을 할당하고, 블록을 통째로 사용하지 쪼개서 사용할지 판단 */
/* bp = 할당 대상으로 선택된 블록의 playload 시작 주소, asize = 그 free block에 할당할 전체 블록 크기 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    remove_free_block(bp);

    if ((csize - asize) >= (2 * DSIZE))
    {
        /* 앞쪽 블록 할당 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* 남은 블록 */
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        /* 남은 free block을 적절한 리스트에 삽입 */
        insert_free_block(bp);
    }
    else
    {
        /* 통째로 할당 */
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














