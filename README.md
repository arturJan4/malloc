# malloc
## Description
fast and efficient malloc algorithm

parts not inside `mm.c` (main malloc aloritm) were provided by the lecturer!, also some CSAPP libraries were used 

## Features
- uses implicit list of free blocks divided into segments (each for a power of 2)
- each segment is a linked list
- information is encoded in headers and footers of blocks (no mallocs used in writing this malloc!)
- performs careful padding for blocks to multiple of `ALIGNMENT` constant
- finds first free block on appropiate segment for a given allocation
- uses a prologue and epilogue block for blocks heap which are preallocated (with some additional free space) at the start of the program
- might perform split on allocation and coalescence on freeing
- optimized reallocation
- invariant checker for debugging purposes to run and check for bugs inbetween allocations and deallocations

## How to run
`make` -> for building whole project   
`make clean` -> to clean directory from executable and object files  
`make format` -> to format all .c files  
`make test` -> to run test provided by the lecturer (sometimes may fail)  

