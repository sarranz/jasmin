jasminc -arch acc "$1" -o main.s
acc-as main.s -o main.o
acc-as start.s -o start.o
acc-ld start.o main.o -o start.elf
acc-sim -v start.elf --dump-regs regs.txt
rm main.o start.o start.elf
cat regs.txt
rm regs.txt
