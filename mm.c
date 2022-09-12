/*
  Artur Jankowski, indeks: 317928
  Oświadczam, że jestem jednym autorem kodu źródłowego.
  Niektóre fragmenty zostały zaczerpnięte z rozwiązań zawartych w dostarczonych
  przez prowadzącego plikach "mm.c", "mm-implicit.c" oraz w rozdziale 9.9
  CSAPP.

  Program wykorzystuje implicit listę wolnych bloków podzieloną na segmenty
  względem rozmiaru bloków (potęgi 2).
  =============================================================================

  Zajęty blok pamięci:
  - nagłówek rozmiaru 4 bajtów zawierający:
    - rozmiar obecnego bloku (wielokrotność 16 -> dzięki czemu mamy wolne dolne
  bity),
    - bit "dwójek" - prevfree -> czy poprzedni blok na stercie jest wolny?,
    - bit "jedynek" - used -> opisuje czy blok jest zajęty,
  - payload wyrównany do wielokrotności ALIGNMENT,
  - możliwy padding, by wyrównać długość bloku do wielokrotności ALIGNMENT.
  =============================================================================

  Wolny blok pamięci:
  - nagłówek (jak w zajętym),
  - wskaźnik prev -> wskazuje na poprzedni element na liście wolnych bloków,
  - wskaźnik next -> wskazuje na następny element na liście wolnych bloków,
  - padding,
  - stopka (która jest powielonym nagłówkiem).

  Dzięki zapisaniu początkowego rozmiaru sterty można określać wskaźniki
  względem tego początku i kompresować je do 4 bajtów
  =============================================================================

  Segmenty:
  Dla każdego segmentu ustalamy strażnika, czyli blok minimalnego rozmiaru,
  który nie zostanie nigdy wybrany przez algorytm poszukujący wolnego bloku
  (w nagłówku ma rozmiar 0).

  Każdy segment to lista dwukierunkowa, strażnik pomaga w uniknięciu przypadków
  brzegowych przy usuwaniu jedynego elementu, dodawaniu pierwszego itp.

  Do kolejnych segmentów trafiają bloki rozmiarów:
  {16}, {32}, {48, 64}, {76, ..,128} etc. aż do {32768, +nieskończoność}
  =============================================================================

  Zawartość sterty (heap):
  Początkowo strażnicy dla każdego segmentu (adresy podzielne przez 16)
  potem wyrównanie do 12 (tak, by po nagłówku payload był wyrównany do 16)
  potem blok prologu rozmiaru 16,
  a następnie blok epilogu (sam nagłówek) rozmiaru 4

  Pomiędzy blokiem prologu i epilogu na start programu tworzę wolny blok pamięci
  rozmiaru 512 bajtów.

  Blok prologu i epilogu podobnie jak strażnicy służą do unikania przypadków
  brzegowych (w tym przypadku przy koalescencji).
  Epilog staje się nagłówkiem nowego bloku przy rozszerzaniu sterty
  (extend_heap).
  =============================================================================

  Przydział bloku:
  Obliczamy wymagany rozmiar bloku i szukamy pierwszego pasującego rozmiarem
  bloku. Szukanie rozpoczynamy w odpowiednim segmencie, jeśli nie znajdziemy
  bloku przechodzimy do segmentu z większymi blokami i tak aż skończą się wolne
  bloki.

  Jeśli znaleźliśmy blok to go alokujemy i potencjalnie wykonujemy podział
  (jeśli jest wystarczająco duży) i nowy wolny blok trafia na listę segmentów.

  Jeśli nie znaleźliśmy pasującego wolnego bloku to rozszerzamy stertę (i
  wykonujemy potencjalnie podział -> wtedy nowy blok trafia do segmentu), wtedy
  może też wydarzyć się koalescencja (ostatni blok przed epilogiem z dużym
  prawdopodobieństwem jest wolny).
  =============================================================================

  Zwalnianie bloku:
  Zwalniamy dany blok, ustawiamy flagę "prevfree", wykonujemy możliwą
  koalescencję i dodajemy blok na listę wolnych bloków.
  =============================================================================

  Realokacja:
  Mamy 3 specjalne przypadki (oprócz oczywistych size==0, i old_ptr==NULL):
  1) nowy rozmiar bloku jest mniejszy:
     wystarczy zwrócić stary wskaźnik
  2) następny blok jest wolny:
     sprawdzamy czy suma obecnego rozmiaru i następnego jest wystarczająca,
     jeśli tak to wykonujemy koalescencję i realokujemy
  3) następny blok to epilog:
     po prostu rozszerzamy stertę

  w.p.p. wykonujemy malloca
*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

// change order of adding to the list of free blocks
//#define LIFO
#define FIFO

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

/* --=[ global definitions ]=----------------------------------------------- */
typedef int32_t word_t; /* Heap is basically an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

#define CHUNKSIZE (1 << 9)
#define SEGMENTS 12

static char *heap_zero;     /* Address of first byte on the heap */
static word_t *heap_start;  /* Address of the first block */
static word_t *heap_end;    /* Address past last byte of last block */
static word_t *last;        /* Points at last block */
static word_t *segfit_list; /* First segment */

/* --=[ boundary tag handling ]=-------------------------------------------- */
/* Given boundary tag return size of whole block (incl. header and footer). */
static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

/* Given boundary tag check if given block is used. */
static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

/* Given boundary tag check if given block is used. */
static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag footer address calculate it's buddy address. */
static inline word_t *bt_header(word_t *bt) {
  return (word_t *)((char *)bt - bt_size(bt) + sizeof(word_t));
}

/* Given boundary tag header address calculate it's buddy address. */
// addendum: void* arithmetic is undefined!
static inline word_t *bt_footer(word_t *bt) {
  return (word_t *)((char *)bt + bt_size(bt) - sizeof(word_t));
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size;
  *bt |= flags;

  // add footer tag
  if (flags == FREE) {
    *bt_footer(bt) = (size | flags);
  }
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt == last) // epilogue
    return NULL;

  return (word_t *)((char *)bt + bt_size(bt));
}

/* Returns address of previous block's footer. */
static inline word_t *bt_prev_footer(word_t *bt) {
  return bt - 1;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start) // prologue
    return NULL;

  return bt_header(bt_prev_footer(bt));
}

/* --=[ optimized tag handling ]=------------------------------------------- */
/* Given boundary tag return prevfree flag. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

/* Given boundary tag clear prevfree flag. */
static inline void bt_clr_prevfree(word_t *bt) {
  if (bt) // ~PREVFREE -> 0 na drugim bicie
    *bt &= ~PREVFREE;
}

/* Given boundary tag set prevfree flag. */
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* --=[ explicit free list handling ]=-------------------------------------- */
/*
  heap_zero is the start of the heap
  we can use relative pointers that are 4 bytes each (instead of 8)
  we assume those function are called on free blocks of minimal size 16
*/

/* Given boundary tag and block address set is as previous in the free list. */
static inline void bt_list_setprev(word_t *bt, word_t *bt_prev) {
  // move to 2nd word of bt
  *(bt + 1) = (char *)bt_prev - heap_zero;
}

/* Given boundary tag and block address set is as next in the free list. */
static inline void bt_list_setnext(word_t *bt, word_t *bt_next) {
  *(bt + 2) = (char *)bt_next - heap_zero;
}

/* Given boundary tag return previous block on the free list. */
static inline word_t *bt_list_getprev(word_t *bt) {
  return (word_t *)(*(bt + 1) + heap_zero);
}
/* Given boundary tag return next block on the free list. */
static inline word_t *bt_list_getnext(word_t *bt) {
  return (word_t *)(*(bt + 2) + heap_zero);
}

static inline word_t *segfit_fromnum(uint num);
static inline uint segfit_select(size_t size);

// add to list of free blocks (LIFO)
#ifdef LIFO
static inline void bt_list_add(word_t *bt) {
  word_t *heap_list = segfit_fromnum(segfit_select(bt_size(bt)));
  word_t *old_first = bt_list_getnext(heap_list); // next of guard

  bt_list_setnext(bt, old_first);
  bt_list_setprev(old_first, bt);

  bt_list_setnext(heap_list, bt); // guard points to current
  bt_list_setprev(bt, heap_list); // current poinst to guard
}
#endif

// FIFO (add to end of queue) -> best results
#ifdef FIFO
/* Add block given by boundary tag to suitable segfit list. */
static inline void bt_list_add(word_t *bt) {
  // select correct segfit list guard
  word_t *heap_list = segfit_fromnum(segfit_select(bt_size(bt)));
  word_t *old_last = bt_list_getprev(heap_list); // prev of guard

  // re-bind previous last element
  bt_list_setnext(old_last, bt);
  bt_list_setprev(bt, old_last);

  bt_list_setnext(bt, heap_list); // current points to guard
  bt_list_setprev(heap_list, bt); // guard points to current
}
#endif

/* Remove block given by boundary tag from segfit list. */
static inline void bt_list_remove(word_t *bt) {
  // get prev and next free block
  word_t *prev = bt_list_getprev(bt);
  word_t *next = bt_list_getnext(bt);

  // remove middle element by omitting
  bt_list_setnext(prev, next);
  bt_list_setprev(next, prev);
}

/* --=[ segfits handling ]=------------------------------------------ */
/* Initalize segments by creating guards starting at address start_addr. */
static inline void segfit_init(word_t *start_addr) {
  segfit_list = start_addr;
  word_t *current; // current segment

  for (int i = 0; i < SEGMENTS; ++i) {
    // i-th guard address
    current = start_addr + 4 * i;

    bt_make(current, ALIGNMENT, FREE);
    *current = 0; // reset size (to disallow being picked on find-fit)

    // guard points to itself
    bt_list_setnext(current, current);
    bt_list_setprev(current, current);
  }
}

/* Return address of appropriate guard given it's number (0 indexed). */
static inline word_t *segfit_fromnum(uint num) {
  return segfit_list + num * 4;
}

/* Given size of the block find correct segment number. */
static inline uint segfit_select(size_t size) {
  size_t curr_size = ALIGNMENT; // minimal block size

  for (uint i = 0; i < SEGMENTS - 1; ++i) {
    if (size <= curr_size) {
      return i;
    }
    curr_size *= 2;
  }

  return SEGMENTS - 1; // largest segment (sizes to infinity)
}

/* --=[ miscellanous procedures ]=------------------------------------------ */
/* Given size in bytes round up to a multiple of ALIGNMENT. */
static inline size_t round_up(size_t size) {
  // (size + 15) & (111111......111110000)
  // cut of 4 lower bits -> (1,2,4,8)
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Calculates block size incl. header, footer & payload,
 * given size in bytes
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  size_t val = size + sizeof(word_t); // payload + header
  val = (val < ALIGNMENT)
          ? ALIGNMENT // have space for at least a footer and header
          : val;

  return round_up(val);
}

/* Extend heap by size bytes. */
static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/* Possibly calesce free block with previous and next on the heap */
static inline void *coalesce(void *bt) {
  // check allocation status of blocks
  int prev_free = (bt_get_prevfree(bt) == PREVFREE);
  int next_free = bt_free(bt_next(bt));
  word_t curr_size = bt_size(bt);

  // no allocation
  if (!prev_free && !next_free) {
    // bt is now free so update prevfree flag of next block.
    bt_set_prevfree(bt_next(bt));

    return bt;
  }

  // coalesce "forward"
  if (!prev_free && next_free) {
    curr_size += bt_size(bt_next(bt));

    // remove next block from list of free blocks
    bt_list_remove(bt_next(bt));

    // create new bigger block
    bt_make(bt, curr_size, FREE);
    return bt;
  }

  // coalesce backward
  if (prev_free && !next_free) {
    curr_size += bt_size(bt_prev(bt));

    // remove prev block from list of free blocks
    bt_list_remove(bt_prev(bt));

    // create new bigger block (check if prev of current prev was free)
    bt_make(bt_prev(bt), curr_size, FREE | bt_get_prevfree(bt_prev(bt)));
    bt_set_prevfree(bt_next(bt));

    return bt_prev(bt);
  }

  // coalesce both
  if (prev_free && next_free) {
    curr_size += (bt_size(bt_next(bt)) + bt_size(bt_prev(bt)));

    // remove prev && next block from list of free blocks
    bt_list_remove(bt_prev(bt));
    bt_list_remove(bt_next(bt));

    // create new bigger block (check if prev of current prev was free)
    bt_make(bt_prev(bt), curr_size, FREE | bt_get_prevfree(bt_prev(bt)));

    return bt_prev(bt);
  }

  // should not happen, but must return something
  return NULL;
}

/* extend heap by EXACTLY (expecting correct alignment) size bytes. */
static inline void *extend_heap(size_t size) {
  char *bt;
  if ((bt = morecore(size)) == NULL) {
    return NULL;
  }
  word_t *new_bt = last;

  // create new block using prev epilogue as header
  bt_make(new_bt, size, FREE | bt_get_prevfree(last));

  // create new epilogue block
  last = (word_t *)(((char *)new_bt) + size);
  heap_end = (word_t *)(last + 1);
  bt_make(last, sizeof(word_t), USED | PREVFREE);

  // possibly coalesce blocks
  void *res = coalesce(new_bt);

  // add new free block to list of free blocks
  bt_list_add((word_t *)res);
  return res;
}

/* --=[ mm_init ]=---------------------------------------------------------- */
int mm_init(void) {
  // heap alignment (for header placement - 12 bytes)
  // ALIGNMENT * SEGMENTS -> array of segments (guards)
  // ALIGNMENT - prologue block
  // sizeof(word_t) - epilogue block -> header only
  void *ptr = morecore(ALIGNMENT - sizeof(word_t) + ALIGNMENT * SEGMENTS +
                       ALIGNMENT + sizeof(word_t));
  if (!ptr)
    return -1;
  // save start of heap (for relative ptr calculations)
  heap_zero = (char *)ptr;

  // initialize segfit segments
  segfit_init((word_t *)((char *)heap_zero));

  // prologue block (USED & 16 bytes)
  heap_start = (word_t *)((char *)heap_zero + ALIGNMENT - sizeof(word_t) +
                          ALIGNMENT * SEGMENTS);
  bt_make(heap_start, ALIGNMENT, USED);

  // epilogue block (USED & 4 bytes -> only header)
  last = NULL;
  last = bt_next(heap_start);
  bt_make(last, 0, USED);

  // byte past epilogue (end of our heap)
  heap_end = (void *)last + sizeof(word_t);

  // add a free block between prologue and epilogue
  if ((extend_heap(CHUNKSIZE) == NULL))
    return -1;

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */
/* First fit strategy. */
static word_t *find_fit(size_t reqsz) {
  // go through segments starting from suitable one
  for (uint i = segfit_select(reqsz); i < SEGMENTS; ++i) {
    word_t *heap_list = segfit_fromnum(i);
    word_t *bt = bt_list_getnext(heap_list); // start of list (a guard)

    // check for guard
    while (bt != heap_list) {
      if (reqsz <= bt_size(bt)) {
        return bt;
      }
      bt = bt_list_getnext(bt);
    }
  }
  // suitable block was not found
  return NULL;
}

/* Allocate given block and possibly split. */
static inline void place(word_t *bt, size_t reqsize) {
  size_t additional_size = bt_size(bt) - reqsize;

  bt_list_remove(bt);

  // worth splitting
  if (additional_size >= ALIGNMENT) {
    bt_make(bt, reqsize, USED | bt_get_prevfree(bt));

    // split
    bt_make(bt_next(bt), additional_size, FREE);
    bt_list_add(bt_next(bt));
  } else {
    bt_make(bt, bt_size(bt), USED | bt_get_prevfree(bt));
    bt_clr_prevfree(bt_next(bt));
  }
}

void *malloc(size_t size) {
  /* Optimization based on binary pattern.
     Detect binary pattern and allocate a block of size equal to a sum of two
     prev allocations when the current allocation is the bigger one.

  */
  static size_t called = 0;
  static size_t prev0 = 0, prev1 = 1, prev2 = 2, prev3 = 3;

  switch (called++ % 4) {
    case 0:
      prev0 = size;
      break;
    case 1:
      prev1 = size;
      break;
    case 2:
      prev2 = size;
      break;
    case 3:
      prev3 = size;
      break;
  }

  size_t real_size;
  // it's a 1010 pattern instead of 0000
  if (prev0 == prev2 && prev1 == prev3 && prev0 != prev1) {
    // we currently allocate the bigger block
    if (prev0 <= size && prev1 <= size)
      real_size = blksz(prev0 + prev1);
    else
      real_size = blksz(size);
  } else {
    // normal allocation
    real_size = blksz(size);
  }

  word_t *bt;

  if (size == 0)
    return NULL;

  bt = (word_t *)find_fit(real_size);
  if (bt != NULL) {
    place((word_t *)bt, real_size);
    return bt_payload(bt);
  }

  // suitable free block was not found -> extend heap
  size_t extend_size = (real_size <= CHUNKSIZE) ? CHUNKSIZE : real_size;

  if ((bt = extend_heap(extend_size)) == NULL)
    return NULL;

  place((word_t *)bt, real_size);

  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */
void free(void *ptr) {
  if (ptr == NULL) {
    return;
  }

  word_t *bt = bt_fromptr(ptr);
  word_t size = bt_size(bt);

  // free the block and coalesce
  bt_make(bt, size, FREE | bt_get_prevfree(bt));
  void *res = coalesce(bt);

  // add it to list of free blocks
  bt_list_add((word_t *)res);
}

/* --=[ realloc ]=---------------------------------------------------------- */
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *bt = bt_fromptr(old_ptr);
  size_t old_size = bt_size(bt);
  size_t real_size = blksz(size);

  // special case 1
  // if new size is smaller then old_size (we don't want to shrink)
  if (real_size <= old_size) {
    return old_ptr;
  }

  // special case nr. 2 - next block is free (and not epilogue)
  // and of enough size
  // then coalesce forward & maybe split
  if (bt_next(bt) != NULL && bt_free(bt_next(bt))) {

    word_t additional_size =
      bt_size(bt_next(bt)) + bt_size(bt) - (word_t)real_size;

    // there is enough space
    if (additional_size >= 0) {
      // next block was free so it was on list -> remove it
      bt_list_remove(bt_next(bt));

      // worth splitting (additional size is a minimum size of a block)
      if (additional_size >= ALIGNMENT) {
        bt_make(bt, real_size, USED | bt_get_prevfree(bt));

        // split
        bt_make(bt_next(bt), (word_t)additional_size, FREE);
        bt_list_add(bt_next(bt));
      } else {

        bt_make(bt, real_size, USED | bt_get_prevfree(bt));
        bt_clr_prevfree(bt_next(bt));
      }

      return old_ptr;
    }
  }

  // special case nr. 3 - last block -> just extend heap
  if (bt_next(bt) == NULL) {
    size_t remainder_space = real_size - bt_size(bt);

    size_t extend_size =
      (remainder_space <= CHUNKSIZE) ? CHUNKSIZE : remainder_space;
    if ((bt = extend_heap(extend_size)) == NULL)
      return NULL;

    bt_make(bt, real_size, USED);
    bt_clr_prevfree(bt_next(bt));

    return old_ptr;
  }

  /* Not any other special case -> just use malloc! */

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  memcpy(new_ptr, old_ptr, old_size - sizeof(word_t));

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */
void mm_checkheap(int verbose) {
  // invariants to check (ideas):
  // 1. all payloads are aligned to 16
  // 2. prev and current allocated flag match
  // 3. there are no 2 free adjacent blocks
  // 4. all headers/footers are in heap range
  // 5. there are prologue/epilogue blocks at start/end
  // 6. all free blocks on list of free blocks are also on the heap
  // 7. all free blocks on the heap are also in the list
  // 8. all block on free list are actually free
  // 9. next/prev ptr's match on the list
  // 10. no cycles (tortoise & hare algorithm etc.)
  // 11. segregated list contains only block that belong to the size class

  if (verbose) {
    printf("checkheap called\n");

    // word-by-word (each of which is 4 bytes)
    // skip for now (too long of an output)
    word_t *startword = heap_start;
    word_t *endword = heap_start;
    printf("HEAP:\n");
    word_t *bt = startword;
    int i = 1;

    while (bt < endword) {
      printf("i: %d, addr: %p, val: %x\n", i++, bt, *bt);
      bt += 1;
    }

    // all blocks on the heap (used or not)

    printf("Blocks:\n");
    bt = heap_start;
    i = 1;

    while ((bt != NULL) && (bt < heap_end)) {
      printf("i: %d, addr: %p, val: %x, size: %d, allocated: %d, prev: %d\n",
             i++, bt, *bt, bt_size(bt), bt_used(bt), bt_get_prevfree(bt));
      bt = bt_next(bt);
    }

    // list of free blocks
    printf("Free list:\n");

    for (uint j = 0; i < SEGMENTS; ++j) {
      printf("SEGEMNT nr %d: ", j);
      i = 1;
      word_t *heap_list = segfit_fromnum(j);
      bt = heap_list; // start of list

      // check for guard
      printf("guard: ");
      printf(
        "addr: %p, val: %x, size: %d, allocated: %d, prevfree: %d, next: %p, "
        "prev: %p\n",
        bt, *bt, bt_size(bt), bt_used(bt), bt_get_prevfree(bt),
        bt_list_getnext(bt), bt_list_getprev(bt));

      bt = bt_list_getnext(bt);
      while (bt != heap_list) {
        printf(
          "i: %d, addr: %p, val: %x, size: %d, allocated: %d, prevfree: %d, "
          "next: %p, prev: %p\n",
          i++, bt, *bt, bt_size(bt), bt_used(bt), bt_get_prevfree(bt),
          bt_list_getnext(bt), bt_list_getprev(bt));
        bt = bt_list_getnext(bt);
      }
    }
  }

  // check alignment and size
  word_t *start = heap_start + 4;
  while ((start != NULL) && (start < last)) {
    if ((bt_size(start) % 16) != 0) {
      printf("block %p size is not a multiple of 16: %d\n", start,
             bt_size(start));
      return;
    }

    if (((long)bt_payload(start) % 16) != 0) {
      printf("block %p is not aligned to 16: (%p)\n", start, bt_payload(start));
      return;
    }
    start = bt_next(start);
  }

  // check for adjacent free blocks
  int free = 0;
  start = heap_start + 4; // skip prologue
  while ((start != NULL) && (start < last)) {
    if (bt_get_prevfree(start) == PREVFREE && !free) {
      printf("block %p is not free but is marked free in: %p\n",
             bt_header(bt_prev_footer(start)), start);
      return;
    }

    if (bt_get_prevfree(start) != PREVFREE && free) {
      printf("block %p is free but is not marked free in: %p\n",
             bt_header(bt_prev_footer(start)), start);
      return;
    }

    int curr_free = !bt_used(start);
    if (free && curr_free) {
      printf("block %p is adjacent to previous free block\n", start);
      return;
    }

    free = curr_free;
    start = bt_next(start);
  }

  // all blocks on free list are actually free
  for (uint i = segfit_select(0); i < SEGMENTS; ++i) {
    // go through segments

    word_t *heap_list = segfit_fromnum(i);
    word_t *bt = bt_list_getnext(heap_list); // start of list (a guard)

    // check for guard
    while (bt != heap_list) {
      if (bt_used(bt)) {
        printf("block %p is on free list but is not actually free\n", bt);
        return;
      }
      bt = bt_list_getnext(bt);
    }
  }

  // segregated list segment contains only block that belong to the size class
  size_t prev_size = 0;
  size_t curr_size = ALIGNMENT; // minmal block size

  for (uint i = 0; i < SEGMENTS; ++i) {
    word_t *heap_list = segfit_fromnum(i);
    word_t *bt = bt_list_getnext(heap_list); // start of list (a guard)

    // check for guard
    while (bt != heap_list) {
      size_t curr_bt_size = bt_size(bt);
      if (curr_bt_size > curr_size || curr_bt_size <= prev_size) {
        printf("block %p has size %ld and is on list of nr %d\n", bt,
               curr_bt_size, i);
      }

      bt = bt_list_getnext(bt);
    }

    prev_size = curr_size;
    curr_size *= 2;
  }
}