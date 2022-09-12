# malloc
## Description
fast and efficient malloc() algorithm (and of course free(), calloc(), realloc())

parts not inside `mm.c` (main malloc alorithm) were provided by the lecturer!, also some CSAPP libraries were used 

## Features
This project was complicated, because I couldn't use dynamic memory allocation here, so the data structure must be hidden inside the memory heap. Also alignments must be calculated carefully or you get some nasty, hard to find errors (drawing and using invariant checker helped). Also, trying to optimize it against given memory traces was fun!

- uses implicit list of free blocks divided into segments (each for a power of 2)
- each segment is a linked list (FIFO)
- information is encoded in headers and footers of blocks (no mallocs used in writing this malloc!)
- performs careful padding for blocks to multiple of `ALIGNMENT` constant
- finds first free block (first-fit) on appropiate segment for a given allocation
- uses a prologue and epilogue block for blocks heap which are preallocated (with some additional free space) at the start of the program
- extending heap by a larger value expecting more allocations
- might perform split on allocation and coalescence on freeing
- optimized reallocation
- some tricks optimized for memory usage patterns provided by the lecturer
- profiled for different variations of the algorithm (best-fit instead of first-fit, LIFO vs FIFO etc.)
- invariant checker for debugging purposes to run and check for bugs inbetween allocations and deallocations

## How to run
`make` -> for building whole project   
`make clean` -> to clean directory from executable and object files  
`make format` -> to format all .c files  
`make test` -> to run test provided by the lecturer (sometimes may fail)  

