ARMGNU = arm-none-eabi
#ARMGNU = arm-linux-gnueabi



AOPS = --warn --fatal-warnings -mcpu=cortex-m0
COPS = -std=gnu11 -Wall -Os -nostdlib -nostartfiles -ffreestanding -mcpu=cortex-m0

# optimize whole program getting rid of e.g. auxiliary functions
#COPS += -fwhole-program

all : asm build kvasir.bin asm/main.asm asm/uart.asm asm/crypto.asm

clean:
	rm -f *.bin *~ *.o *.elf *.list *.asm asm/* build/*

asm:
	mkdir asm
build:
	mkdir build
#---------------------------------

build/flash.o : flash.s
	$(ARMGNU)-as $(AOPS) flash.s -o build/flash.o

build/main.o : main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -c main.c -o build/main.o
build/uart.o : uart.c uart.h
	$(ARMGNU)-gcc $(COPS) -mthumb -c uart.c -o build/uart.o
build/crypto.o : crypto.c crypto.h
	$(ARMGNU)-gcc $(COPS) -mthumb -c crypto.c -o build/crypto.o

asm/main.asm : main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c main.c -o asm/main.asm
asm/uart.asm : uart.c uart.h
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c uart.c -o asm/uart.asm

asm/crypto.asm : crypto.c crypto.h
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c crypto.c -o asm/crypto.asm

kvasir.bin : flash.ld build/flash.o build/main.o build/uart.o build/crypto.o
	$(ARMGNU)-ld -o build/kvasir.elf -T flash.ld build/flash.o build/main.o build/uart.o build/crypto.o
	$(ARMGNU)-objdump -d build/kvasir.elf > build/kvasir.list
	$(ARMGNU)-objdump -j .rodata -s build/kvasir.elf >> build/kvasir.list
	$(ARMGNU)-objcopy build/kvasir.elf build/kvasir.bin -O binary
	cp build/kvasir.bin kvasir.bin 
