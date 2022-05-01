/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: 20190439 OH SEUNGHUN
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*Basic constants and macros*/
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define CHUNKSIZE (1<<12)    // extend size
#define INITCHUNKSIZE (1<<6)

#define MAX_SEG 20           // number of segregate list
#define MAX(x, y) ((x) > (y) ? (x) : (y))       // MAX of x or y
#define MIN(x, y) ((x) < (y) ? (x) : (y))       // MIN of s or y

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val)       (*(unsigned int *)(p) = (val))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// Address of free block's next and previous block's entry
#define GET_PREV(ptr) ((char *)(ptr))
#define GET_NEXT(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's next and previous blocks on the segregated list 
#define GET_PREV_BLK(ptr) (*(char **)(ptr))
#define GET_NEXT_BLK(ptr) (*(char **)(GET_NEXT(ptr)))

//set the prev and next field of bp to address nbp
#define PUT_PTR(p, ptr)  (*(unsigned int *)(p) = (unsigned int)(ptr))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static void* find_fit(size_t asize);
static void* place(void* bp, size_t asize);
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void insert_seg_list(void* bp, size_t asize);
static void delete_seg_list(void* bp);
int ret_seg_index(size_t asize);

void** seglist;
/*
    This function return the number of index that asize is fit in
*/
int ret_seg_index(size_t asize)
{
	int i = 0;
    size_t compare_size = 1;
    for (i = 0; i < MAX_SEG; i++)
    {
        if (compare_size >= asize)
        {
            break;
        }
        compare_size <<= 1;
    }
    
    return i;
}
/*
    This function insert the pointer bp to seg_list. Asize is the size of demanding size that user wanted.
    First find the index of list_index and then we should find the block that fit in between the seg_list[index].
    Then we divide the case total 4.
    Case1 prev_node != NULL && tempt_node != NULL
    Case2 prev_node == NULL && tempt_node != NULL
    Case3 prev_node != NULL && tempt_node == NULL
    Case4 prev_node == NULL && tempt_node == NULL
    It should divide because some case should be insert the block to seglist directly. 
*/
static void insert_seg_list(void* bp, size_t asize)
{   
    void* find_node = bp;
    void* prev_node = NULL;
    int list_index = ret_seg_index(asize);

    find_node = seglist[list_index];
    while (1)
    {
        if ((find_node == NULL) || (GET_SIZE(HDRP(find_node)) >= asize))
        {
            break;
        }
        prev_node = find_node;
        find_node = GET_PREV_BLK(find_node);
    }


    if (find_node != NULL)
    {
        PUT_PTR(GET_PREV(bp), find_node);
        PUT_PTR(GET_NEXT(find_node), bp);
        PUT_PTR(GET_NEXT(bp), prev_node);
        if (prev_node != NULL)
        {
            PUT_PTR(GET_PREV(prev_node), bp);
        }
        else
        {
            seglist[list_index] = bp;
        }
    }
    else
    {
        PUT_PTR(GET_PREV(bp), NULL);
        PUT_PTR(GET_NEXT(bp), prev_node);
        if (prev_node != NULL)
        {
            PUT_PTR(GET_PREV(prev_node), bp);
        }
        else
        {
            seglist[list_index] = bp;
        }
    }
    return;

}
/*
    This function is for deleting the bp in the seg_list.
    First find the index of the bp that fit in the seg_list. Then we should do is connecting the prev block and next block.
    prev block's next block should be next block. next block's prev block should be previous block. We divide the case because
    sometimes we should directly insert the block to seglist.
*/
static void delete_seg_list(void* bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int list_index = ret_seg_index(size);

    if (GET_PREV_BLK(bp) != NULL)
    {
        PUT_PTR(GET_NEXT(GET_PREV_BLK(bp)), GET_NEXT_BLK(bp));
        if (GET_NEXT_BLK(bp) != NULL)
        {
            PUT_PTR(GET_PREV(GET_NEXT_BLK(bp)), GET_PREV_BLK(bp));
        }
        else
        {
            seglist[list_index] = GET_PREV_BLK(bp);
        }
    }
    else
    {
        if (GET_NEXT_BLK(bp) != NULL)
        {
            PUT_PTR(GET_PREV(GET_NEXT_BLK(bp)), NULL);
        }
        else
        {
            seglist[list_index] = NULL;
        }
    }

    return;
}
/*
    This function is made by first_fit method.
    First find the block that we can use. If our block is unusing ,unreallocating and it is enough size for fit in the our block then we should use that block.
    There's no block fit in then return NULL.
*/
static void* find_fit(size_t asize)
{
    size_t compare_size = 1;
    void* find_node;
    int i = 0;
    for (i = 0; i < MAX_SEG; i++)
    {
        if (compare_size < asize)
        {
            compare_size = compare_size << 1;
            continue;
        }
        else
        {
            find_node = seglist[i];
            while (1)
            {
                if (find_node == NULL)
                {
                    break;
                }
                if ((GET_SIZE(HDRP(find_node)) >= asize) && (GET_ALLOC(find_node) == 0) && (GET_TAG(find_node) == 0))
                {
                    return find_node;
                }
                find_node = GET_PREV_BLK(find_node);
            }
            if (find_node != NULL)
            {
                break;
            }
        }
        compare_size = compare_size << 1;
    }

    return NULL;
}
/*
    Place function should split the block. There are many sizes of blocks but there are few blocks that are exactly equal size of we demand.
    So our block might be not equal size that we demand. So we should split the block that we don't use. If the block_size and demanding sizes difference is smaller than twice as double size
    then we can not use that block so don't split. However the size is bigger or equal than twice as double size, then we can use that unusing block So split the block and insert to free block.
*/
static void* place(void* bp, size_t asize)
{
    size_t block_size = GET_SIZE(HDRP(bp));

    delete_seg_list(bp);

    if ((block_size - asize) <= 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
    else if (asize >= 100)
    {
        PUT(HDRP(bp), PACK(block_size - asize, 0));
        PUT(FTRP(bp), PACK(block_size - asize, 0));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        insert_seg_list(bp, block_size - asize);
        return NEXT_BLKP(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        insert_seg_list(NEXT_BLKP(bp), block_size - asize);
    }
    return bp;
}
/*
    coalescing is needed when there is physically prev block and next block is unallocated. Then we can attach the block as one unallocated block.
    coalescing has 4 cases.
    Case1 prev_block allocated && next_block allocated
    Case2 prev_block allocated && next_block unallocated
    Case3 prev_block unallocated && next_block allocated
    Case4 prev_block unallocated && next_block unallocated
*/
static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;

    if ((prev_alloc == 1) && (next_alloc == 1))         /*Case 1*/
    {
        return bp;
    }
    else if ((prev_alloc == 1) && (next_alloc == 0))    /*Case 2*/
    {
        delete_seg_list(bp);
        delete_seg_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if ((prev_alloc == 0) && (next_alloc == 1))    /*Case 3*/
    {
        delete_seg_list(bp);
        delete_seg_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if ((prev_alloc == 0) && (next_alloc == 0))    /*Case 4*/
    {
        delete_seg_list(bp);
        delete_seg_list(NEXT_BLKP(bp));
        delete_seg_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_seg_list(bp, size);

    return bp;
}
/*
    This function extend the heap size as ALIGN(words) and should pack new bounding footer
*/
static void* extend_heap(size_t words)
{
    void* bp;
    size_t size;

    size = ALIGN(words);
    if ((bp = mem_sbrk(size)) == (void*)-1)
    {
        return NULL;
    }
    PUT_NOTAG(HDRP(bp), PACK(size, 0));
    PUT_NOTAG(FTRP(bp), PACK(size, 0));
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    insert_seg_list(bp, size);

    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    char* heap_start;

    seglist = mem_sbrk(sizeof(int*) * MAX_SEG);
    for (list = 0; list < MAX_SEG; list++) {
        seglist[list] = NULL;
    }

    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    PUT_NOTAG(heap_start, 0);                            
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); 
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); 
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     

    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void* bp;

    if (size == 0)
    {
        return NULL;
    }

    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = ALIGN(size + DSIZE);
    }

    bp = find_fit(asize);
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);

        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    bp = place(bp, asize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    insert_seg_list(ptr, size);
    coalesce(ptr);
    
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void* new_ptr = ptr;    
    size_t new_size = size; 
    int remainder;          
    int extendsize;         
    int block_buffer;       

    if (ptr == NULL)
    {
        return mm_malloc(size);
    }
    else
    {
        if (size == 0)
        {
            mm_free(ptr);
            return NULL;
        }
        else
        {
            if (size <= DSIZE)
            {
                new_size = 2 * DSIZE;
            }
            else
            {
                new_size = ALIGN(size + DSIZE);
            }
            block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
            if (block_buffer < 0)
            {
                if ((GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) || (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0))
                {
                    remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
                    if (remainder < 0)
                    {
                        extendsize = MAX(-remainder, CHUNKSIZE);
                        if (extend_heap(extendsize) == NULL)
                            return NULL;
                        remainder += extendsize;
                    }

                    delete_seg_list(NEXT_BLKP(ptr));

                    PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
                    PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
                    
                    return ptr;

                }
                else
                {
                    new_ptr = mm_malloc(new_size - DSIZE);
                    memcpy(new_ptr, ptr, MIN(size, new_size));
                    mm_free(ptr);
                    SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
                    return new_ptr;
                }
            }
            return ptr;
        }
    }
}














