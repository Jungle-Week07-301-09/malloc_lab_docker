/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
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
#include <stdint.h>
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

#define WSIZE 4 // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8 // 더블워드 사이즈(bytes)
#define CHUNKSIZE (1 << MAX_LEVEL)  // heap을 이정도 늘린다(bytes)

#define MIN_LEVEL 4
#define MAX_LEVEL 21
#define LEVEL_COUNT (MAX_LEVEL - MIN_LEVEL + 1) // 18개


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

#define LOG(k) ((unsigned int)(log2f((float)k)))
#define INDEX(base, k) ((base+(WSIZE*(k-1))))

#define LOG(k) ((unsigned int)(log2f((float)k)))
#define INDEX(base, level) ((char*)(base) + (level)*WSIZE)

// Given block ptr bp, compute address of next and previous blocks
// 현재 bp에서 WSIZE를 빼서 header를 가리키게 하고, header에서 get size를 한다.
// 그럼 현재 블록 크기를 return하고(헤더+데이터+풋터), 그걸 현재 bp에 더하면 next_bp나옴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// base_listp 에서 level 번째 슬롯의 주소(&head)를 리턴
#define HEAD_PTR(level)   ((void **)((char *)base_listp + (level) * WSIZE))

// level 번째 리스트의 head 값을 읽어올 때
#define HEAD(level)       (*HEAD_PTR(level))

#define PREV(bp) (*(void**)(bp))
#define NEXT(bp) (*(void**)(bp + WSIZE))

#define LOG(k) ((unsigned int)log2f((float)k))
#define INDEX(base, k) (base + (WSIZE*(k-1)))

static void *heap_listp = NULL; // heap 시작주소 pointer
static void *base_listp = NULL; // base list head - 가용리스트 시작부분
// static void *last_bp = NULL; // next_fit을 위한 전역변수

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void* find_buddy(void* bp);
static void _merge_buddy(void* bp, void* buddy);
static void merge_buddy(void*bp);
static void removeBlock(void *bp);
static void putFreeBlock(void *bp);

void removeBlock(void *bp, size_t asize);
void putFreeBlock(void *bp, size_t asize);

int mm_init(void)
{   
    size_t init_bytes = ALIGN(8 + 16 + LEVEL_COUNT * WSIZE + 4); // 104B
    heap_listp = mem_sbrk(init_bytes);
    if (heap_listp == (void *)-1)
        return -1;

    // [0~7] Padding
    PUT(heap_listp + 0 * WSIZE, 0);
    PUT(heap_listp + 1 * WSIZE, 0);

    // [8] Prologue Header (16B 블록)
    PUT(heap_listp + 2 * WSIZE, PACK(2 * DSIZE, 1));  // header [8]
    PUT(heap_listp + 3 * WSIZE, 0);                   // prev [12]
    PUT(heap_listp + 4 * WSIZE, 0);                   // next [16]
    PUT(heap_listp + 5 * WSIZE, PACK(2 * DSIZE, 1));  // footer [20]

    // [24]부터 base_listp
    base_listp = heap_listp + 6 * WSIZE;

    for (int i = 0; i < LEVEL_COUNT; i++) {
        PUT(base_listp + i * WSIZE, 0); 
    }
    // Epilogue Header
    PUT((char*)heap_listp + init_bytes - WSIZE, PACK(0,1)); // [96]

    // 초기 힙 확장 (2MB)
    if (extend_heap(CHUNKSIZE) == NULL)
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

static void* coalesce(void* bp){

}

static void merge_buddy(void* bp){
    void* buddy = find_buddy(bp);
    size_t size = GET_SIZE(HDRP(bp));
    size_t buddy_size = GET_SIZE(HDRP(bp));

    if(!GET_ALLOC(HDRP(buddy)) && (size == buddy_size)){
        void* front = (bp < buddy) ? bp : buddy;
        void* second  = (bp > buddy) ? bp : buddy;
        _merge_buddy(front, second);
        merge_buddy(front);
    }else{
        putFreeBlock(bp);
    }
}

static void _merge_buddy(void* bp, void* buddy){
    size_t bp_size = GET_SIZE(HDRP(bp));
    size_t size = bp_size * 2;
    removeBlock(bp);
    removeBlock(buddy);
    PUT(HDRP(bp),PACK(size, 0));
    PUT(FTRP(buddy), PACK(size, 0));
    putFreeBlock(bp);
}


static void *extend_heap(size_t size)
{
    char *bp;
    size_t block_size = ALIGN(size); // 보통 size = CHUNKSIZE
    int level = level_for_size(block_size); // ex: 2^21 → level 17 (if MIN_LEVEL = 4)

    bp = mem_sbrk(block_size);
    if (bp == (void *)-1)
        return NULL;

    void *cur_bp = bp;
    size_t cur_size = block_size;

    // split down to 최소 버디 크기
    while (level > 0) {
        size_t half = cur_size / 2;

        if (half < (1 << MIN_LEVEL))
            break; // 더 쪼갤 수 없으면 종료

        void *right_bp = (char *)cur_bp + half;

        // 오른쪽 버디 블록 설정
        PUT(HDRP(right_bp), PACK(half, 0));
        PUT(FTRP(right_bp), PACK(half, 0));
        putFreeBlock(right_bp, level_for_size(half));

        // 왼쪽으로 계속 split 진행
        cur_size = half;
        level--;
    }

    // 마지막 블록 삽입
    PUT(HDRP(cur_bp), PACK(cur_size, 0));
    PUT(FTRP(cur_bp), PACK(cur_size, 0));
    putFreeBlock(cur_bp, level_for_size(cur_size));

    // epilogue 설정
    void *epilogue = (char *)bp + block_size;
    PUT(HDRP(epilogue), PACK(0, 1));

    return cur_bp;
}

static int level_for_size(size_t size) {
    size_t block_size = 1 << MIN_LEVEL; // 16B부터 시작
    int level = 0;

    while (level < LEVEL_COUNT && block_size < size) {
        block_size <<= 1; // 곱하기 2
        level++;
    }

    return level; // level 0 ~ 17 (2^4 ~ 2^21)
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


   
    if(size <= 0) 
        return NULL;
    
    
   
    if(size <= DSIZE)
        asize = 2*DSIZE; 
    else         
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1)) / DSIZE);

   
    if((bp = find_fit(asize))!=NULL){
        place(bp,asize); 
        return bp;
    }

  

  
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void putFreeBlock(void *bp, size_t level) {
    void *old_head = HEAD(level);

    // 1) bp.next = old_head
    NEXT(bp) = old_head;
    // 2) bp.prev = NULL
    PREV(bp) = NULL;
    // 3) old_head.prev = bp, (old_head이 NULL 아닐 때만)
    if (old_head)
        PREV(old_head) = bp;
    // 4) head = bp
    HEAD(level) = bp;
}
void removeBlock(void *bp, size_t level) {
    void *next = NEXT(bp);
    void *prev = PREV(bp);

    if (prev) {
        // 중간 또는 tail 제거
        NEXT(prev) = next;
    } else {
        // head 제거
        HEAD(level) = next;
    }

    if (next) {
        // next 블록이 있으면 prev 필드 갱신
        PREV(next) = prev;

    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
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

static void* find_buddy(void* bp){
    size_t size = GET_SIZE(HDRP(bp));
    return (void*)((uintptr_t)bp ^ size);
}