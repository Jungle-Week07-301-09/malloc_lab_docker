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
// @@@@@ explicit @@@@@
#include <sys/mman.h>
#include <errno.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 9",
    /* First member's full name */
    "La_Ska",
    /* First member's email address */
    "flaska99@jungle.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4             // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8             // 더블워드 사이즈(bytes)
#define CHUNKSIZE (1 << 12) // heap을 이정도 늘린다(bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
// pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and wirte a word at address p
// p는 (void*)포인터이며, 이것은 직접 역참조할 수 없다.
#define GET(p) (*(unsigned int *)(p))              // p가 가리키는 놈의 값을 가져온다
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 포인터에 val을 넣는다

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7) // ~0x00000111 -> 0x11111000(얘와 and연산하면 size나옴)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더+데이터+풋터 -(헤더+풋터)

// Given block ptr bp, compute address of next and previous blocks
// 현재 bp에서 WSIZE를 빼서 header를 가리키게 하고, header에서 get size를 한다.
// 그럼 현재 블록 크기를 return하고(헤더+데이터+풋터), 그걸 현재 bp에 더하면 next_bp나옴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PREV(bp) (*(void **)(bp))
#define NEXT(bp) (*(void **)(bp + WSIZE))

static void *heap_listp = NULL; // heap 시작주소 pointer
static void *free_listp = NULL; // free list head - 가용리스트 시작부분
// static void *last_bp = NULL; // next_fit을 위한 전역변수

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

void removeBlock(void *bp);
void putFreeBlock(void *bp);

int mm_init(void)
{
    heap_listp = mem_sbrk(3 * DSIZE);
    if (heap_listp == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0); // Unused padding
    PUT(heap_listp + WSIZE, PACK(2 * DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, NULL);
    PUT(heap_listp + 3 * WSIZE, NULL);
    PUT(heap_listp + 4 * WSIZE, PACK(2 * DSIZE, 1));
    PUT(heap_listp + 5 * WSIZE, PACK(0, 1));

    free_listp = heap_listp + DSIZE;
    // last_bp = free_listp; // next_fit 을 위한 추가
    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
// split_buddy (계속 나눔), find_buddy, merge_buddy
static void split_buddy(void *bp, size_t asize)
{
    // bp의 크기 size를 읽음
    size_t size = GET_SIZE(HDRP(bp));

    while ((size / 2) >= asize && (size / 2) >= 2 * DSIZE)
    {
        size = size / 2;                 // 사이즈 반으로 줄임
        void *buddy = (char *)bp + size; // 버디 주소

        // bp블록에 header/footer 기록
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        // buddy블록에 header/footer 기록
        PUT(HDRP(buddy), PACK(size, 0));
        PUT(FTRP(buddy), PACK(size, 0));

        // free list에 삽입
        putFreeBlock(buddy, LOG(size));
    }
}

// 연결
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈

    // case 1
    // case 2
    if (prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 3
    else if (!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 4
    else if (!prev_alloc && !next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (((bp = mem_sbrk(size)) == (void *)-1))
        return NULL;

    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));         // Free block header
    PUT(FTRP(bp), PACK(size, 0));         // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header

    return coalesce(bp);
}

// static void *find_fit(size_t asize){
//     void *bp;

//     for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT(bp)){
//         if(GET_SIZE(HDRP(bp)) >= asize){
//             return bp;
//         }
//     }
//     return NULL;
// }

// static void *find_fit(size_t asize){ // next_fit 추가
//     void *bp = last_bp;
//     if (bp == NULL) bp = free_listp;

//     // 먼저 last_bp 이후부터 free list 끝까지 검색
//     for (; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT(bp)) {
//         if (GET_SIZE(HDRP(bp)) >= asize) {
//             last_bp = bp;
//             return bp;
//         }
//     }

//     for (bp = free_listp; bp != last_bp; bp = NEXT(bp)) {
//         if (GET_SIZE(HDRP(bp)) >= asize) {
//             last_bp = bp; // 찾았으면 last_bp 업데이트
//             return bp;
//         }
//     }

//     return NULL; // 못 찾으면 NULL
// }

static void *find_fit(size_t asize)
{
    void *bp;
    void *best_bp = NULL;
    size_t best_size = (size_t)-1; // 초기값: 무한대(가장 큰 값)

    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT(bp))
    {
        size_t bsize = GET_SIZE(HDRP(bp));
        if (bsize >= asize)
        {
            if (bsize < best_size)
            {
                best_size = bsize;
                best_bp = bp;
                // 여기서는 무조건 끝까지 본다. (first fit처럼 찾자마자 리턴 안 함)
            }
        }
    }

    return best_bp; // 가장 좋은 블록 리턴 (없으면 NULL)
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    removeBlock(bp);
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size <= 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

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

void putFreeBlock(void *bp)
{
    NEXT(bp) = free_listp;
    PREV(bp) = NULL;
    PREV(free_listp) = bp;
    free_listp = bp;
}

void removeBlock(void *bp)
{
    // last_bp = NEXT(bp);
    if (bp == free_listp)
    {
        PREV(NEXT(bp)) = NULL;
        free_listp = NEXT(bp);
    }
    else
    {
        NEXT(PREV(bp)) = NEXT(bp);
        PREV(NEXT(bp)) = PREV(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }

    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}