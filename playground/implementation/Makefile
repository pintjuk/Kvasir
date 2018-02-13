ARMGNU = arm-none-eabi
#ARMGNU = arm-linux-gnueabi

AOPS = --warn --fatal-warnings -mcpu=cortex-m0
COPS = -std=gnu11 -Wall -Os -nostdlib -nostartfiles -ffreestanding -mcpu=cortex-m0

# optimize whole program getting rid of e.g. auxiliary functions
#COPS += -fwhole-program

all : main.bin main.asm

clean:
	rm -f *.bin *~ *.o *.elf *.list *.asm

#---------------------------------

flash.o : flash.s
	$(ARMGNU)-as $(AOPS) flash.s -o flash.o

main.o : main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -c main.c -o main.o

main.asm : main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c main.c -o main.asm

main.bin : flash.ld flash.o main.o
	$(ARMGNU)-ld -o main.elf -T flash.ld flash.o main.o
	$(ARMGNU)-objdump -d main.elf > main.list
	$(ARMGNU)-objdump -j .rodata -s main.elf >> main.list
	$(ARMGNU)-objcopy main.elf main.bin -O binary
