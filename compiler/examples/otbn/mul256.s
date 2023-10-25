	.global        	_mock
	.global        	mock
_mock:
mock:
	sw             	ra, 0(sp)
	addi           	sp, sp, -4
	bn.xor         	w0, w0, w0, FG0
	bn.not         	w1, w0, FG0
	bn.addi        	w2, w0, 2, FG0
	jal            	ra, Lmul256$1
Lmock$1:
	lw             	ra, 0(sp)
	addi           	sp, sp, 4
	ret            
	.global        	_main
	.global        	main
_main:
main:
	sw             	ra, 0(sp)
	addi           	sp, sp, -4
	bn.xor         	w2, w2, w2, FG0
	bn.mulqacc.z   	w0.0, w1.0, 0
	bn.mulqacc     	w0.0, w1.1, 64
	bn.mulqacc.so  	w2.L, w0.1, w1.0, 64, FG0
	bn.mulqacc     	w0.0, w1.2, 0
	bn.mulqacc     	w0.1, w1.1, 0
	bn.mulqacc     	w0.2, w1.0, 0
	bn.mulqacc     	w0.0, w1.3, 64
	bn.mulqacc     	w0.1, w1.2, 64
	bn.mulqacc     	w0.2, w1.1, 64
	bn.mulqacc.so  	w2.U, w0.3, w1.0, 64, FG0
	bn.mulqacc     	w0.1, w1.3, 0
	bn.mulqacc     	w0.2, w1.2, 0
	bn.mulqacc     	w0.3, w1.1, 0
	bn.mulqacc     	w0.2, w1.3, 64
	bn.mulqacc     	w0.3, w1.2, 64
	bn.mulqacc.wo  	w1, w0.3, w1.3, 128, FG0
	bn.mov         	w0, w2
	lw             	ra, 0(sp)
	addi           	sp, sp, 4
	ret            
Lmul256$1:
	bn.xor         	w0, w0, w0, FG0
	bn.mulqacc.z   	w2.0, w1.0, 0
	bn.mulqacc     	w2.0, w1.1, 64
	bn.mulqacc.so  	w0.L, w2.1, w1.0, 64, FG0
	bn.mulqacc     	w2.0, w1.2, 0
	bn.mulqacc     	w2.1, w1.1, 0
	bn.mulqacc     	w2.2, w1.0, 0
	bn.mulqacc     	w2.0, w1.3, 64
	bn.mulqacc     	w2.1, w1.2, 64
	bn.mulqacc     	w2.2, w1.1, 64
	bn.mulqacc.so  	w0.U, w2.3, w1.0, 64, FG0
	bn.mulqacc     	w2.1, w1.3, 0
	bn.mulqacc     	w2.2, w1.2, 0
	bn.mulqacc     	w2.3, w1.1, 0
	bn.mulqacc     	w2.2, w1.3, 64
	bn.mulqacc     	w2.3, w1.2, 64
	bn.mulqacc.wo  	w1, w2.3, w1.3, 128, FG0
	ret            
