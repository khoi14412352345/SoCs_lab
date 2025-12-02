help:
	@echo available commands: '`make build`', '`make start`' and '`make run`'

build:
	riscv64-unknown-elf-as -march=rv32im -mabi=ilp32 uppercase.S -o uppercase.o
	# Use our custom linker script so everything starts at 0x80000000
	riscv64-unknown-elf-ld -A rv32 --oformat elf32-littleriscv \
		-T link.ld \
		uppercase.o -o uppercase.bin
	riscv64-unknown-elf-objdump -d uppercase.bin > uppercase.disasm.s

start:
	# No -m here – use Spike's default RAM at 0x80000000
	spike -p1 --isa=rv32im -d uppercase.bin

run:
	echo "until pc 0 80000000\n str 0 0x80000100\n rs 1000\n str 0 0x80000100\n quit" | \
		spike -p1 --isa=rv32im -d --debug-cmd=/dev/stdin uppercase.bin

