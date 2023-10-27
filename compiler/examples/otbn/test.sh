jasminc -arch otbn "$1" -o main.s
otbn-as main.s -o main.o
otbn-as start.s -o start.o
otbn-ld start.o main.o -o start.elf
otbn-sim -v start.elf --dump-regs regs.txt
rm main.o start.o start.elf
cat regs.txt
rm regs.txt
