.cpu cortex-m0
.thumb

	
.thumb_func
.global _start
_start:
stacktop: .word 0x20004000
.word reset
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang
.word hang

.thumb_func
reset:
    bl main
    b hang

.thumb_func
hang:   b .

.end

