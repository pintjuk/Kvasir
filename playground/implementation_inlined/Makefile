ARMGNU = arm-none-eabi
#ARMGNU = arm-linux-gnueabi


PROJECT_NAME = kvasir
AUTHORS = Daniil-Pintjuk Adam-Johansson
AOPS = --warn --fatal-warnings -mcpu=cortex-m0
COPS = -std=gnu11 -Wall -Os -nostdlib -nostartfiles -fif-conversion -fno-inline-small-functions -ffreestanding -mcpu=cortex-m0
FILES = uart crypto
BUILD_DIR = build
SORCE_DIR = src
BUILD_PROJECT_NAME=$(BUILD_DIR)/$(PROJECT_NAME)
ASM_DIR = asm
OBJECTS = $(foreach F,  $(FILES), $(BUILD_DIR)/$(F).o)
ASMS = $(foreach F,  $(FILES), $(ASM_DIR)/$(F).asm)

# optimize whole program getting rid of e.g. auxiliary functions
#COPS += -fwhole-program

all : $(ASM_DIR) $(BUILD_DIR) $(PROJECT_NAME).bin $(ASM_DIR)/main.asm $(ASMS) $(BUILD_DIR)/main.o $(OBJECTS)

clean:
	rm -f *.bin *~ *.o *.elf *.list *.asm $(ASM_DIR)/* $(BUILD_DIR)/*

$(ASM_DIR):
	mkdir $@
$(BUILD_DIR):
	mkdir $@
#---------------------------------

$(BUILD_DIR)/flash.o : $(SORCE_DIR)/flash.s
	$(ARMGNU)-as $(AOPS) $< -o $@

$(BUILD_DIR)/main.o : $(SORCE_DIR)/main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -c $< -o $@

$(OBJECTS): $(BUILD_DIR)/%.o : $(SORCE_DIR)/%.c $(SORCE_DIR)/%.h
	$(ARMGNU)-gcc $(COPS) -mthumb -c $< -o $@

$(ASM_DIR)/main.asm : $(SORCE_DIR)/main.c
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c $< -o $@

$(ASMS): $(ASM_DIR)/%.asm : $(SORCE_DIR)/%.c $(SORCE_DIR)/%.h
	$(ARMGNU)-gcc $(COPS) -mthumb -S -c $< -o $@

$(PROJECT_NAME).bin : $(SORCE_DIR)/flash.ld $(BUILD_DIR)/flash.o $(BUILD_DIR)/main.o $(OBJECTS)
	$(ARMGNU)-ld -o $(BUILD_PROJECT_NAME).elf -T $^
	$(ARMGNU)-objdump -d $(BUILD_PROJECT_NAME).elf > $(BUILD_PROJECT_NAME).list
	$(ARMGNU)-objdump -j .rodata -s $(BUILD_PROJECT_NAME).elf >> $(BUILD_PROJECT_NAME).list
	$(ARMGNU)-objcopy $(BUILD_PROJECT_NAME).elf $(BUILD_PROJECT_NAME).elf -O binary
	cp $(BUILD_PROJECT_NAME).elf $@
