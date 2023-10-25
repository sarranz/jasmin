	.global        	_mock
	.global        	mock
_mock:
mock:
	sw             	ra, 0(sp)
	addi           	sp, sp, -4
	add            	x12, sp, x0
	srli           	sp, sp, 3
	slli           	sp, sp, 3
	bn.xor         	w0, w0, w0, FG0
	bn.xor         	w1, w1, w1, FG0
	bn.xor         	w2, w2, w2, FG0
	bn.xor         	w3, w3, w3, FG0
	bn.xor         	w4, w4, w4, FG0
	bn.xor         	w5, w5, w5, FG0
	bn.xor         	w6, w6, w6, FG0
	bn.xor         	w7, w7, w7, FG0
	bn.xor         	w13, w13, w13, FG0
	bn.xor         	w11, w11, w11, FG0
	bn.xor         	w12, w12, w12, FG0
	bn.xor         	w10, w10, w10, FG0
	addi           	sp, sp, 4294967292
	jal            	ra, Lbarrett384$1
Lmock$1:
	bn.mov         	w1, w3
	add            	sp, x12, x0
	lw             	ra, 0(sp)
	addi           	sp, sp, 4
	ret            
	.global        	_main
	.global        	main
_main:
main:
	sw             	ra, 0(sp)
	addi           	sp, sp, -4
	add            	x12, sp, x0
	srli           	sp, sp, 3
	slli           	sp, sp, 3
	bn.xor         	w13, w13, w13, FG0
	bn.xor         	w11, w11, w11, FG0
	bn.xor         	w12, w12, w12, FG0
	bn.xor         	w10, w10, w10, FG0
	addi           	sp, sp, 4294967292
	jal            	ra, Lbarrett384$1
Lmain$1:
	bn.mov         	w1, w3
	add            	sp, x12, x0
	lw             	ra, 0(sp)
	addi           	sp, sp, 4
	ret            
Lbarrett384$1:
	sw             	ra, 0(sp)
	jal            	ra, Lmul384$1
Lbarrett384$4:
	bn.sel         	w9, w7, w13, FG0.M
	bn.sel         	w8, w6, w13, FG0.M
	bn.mov         	w14, w10
	bn.mov         	w15, w12
	bn.rshi        	w0, w13, w11 >> 127
	bn.rshi        	w1, w11, w12 >> 127
	bn.mov         	w3, w7
	bn.mov         	w2, w6
	jal            	ra, Lmul384$1
Lbarrett384$3:
	bn.rshi        	w2, w13, w11 >> 128
	bn.rshi        	w3, w11, w12 >> 128
	bn.add         	w1, w3, w1, FG0
	bn.addc        	w0, w2, w0, FG0
	bn.add         	w1, w1, w9, FG0
	bn.addc        	w2, w0, w8, FG0
	bn.rshi        	w0, w13, w2 >> 1
	bn.rshi        	w1, w2, w1 >> 1
	bn.mov         	w3, w5
	bn.mov         	w2, w4
	jal            	ra, Lmul384$1
Lbarrett384$2:
	bn.sub         	w0, w14, w10, FG0
	bn.subb        	w0, w15, w12, FG0
	bn.sub         	w0, w14, w3, FG0
	bn.subb        	w1, w15, w2, FG0
	bn.sel         	w0, w14, w0, FG0.C
	bn.sel         	w1, w15, w1, FG0.C
	bn.sub         	w3, w0, w3, FG0
	bn.subb        	w2, w1, w2, FG0
	bn.sel         	w3, w0, w3, FG0.C
	bn.sel         	w0, w1, w2, FG0.C
	lw             	ra, 0(sp)
	addi           	sp, sp, 4
	ret            
Lmul384$1:
	bn.mulqacc.z   	w1.0, w3.0, 0
	bn.mulqacc     	w1.0, w3.1, 64
	bn.mulqacc.so  	w10.L, w1.1, w3.0, 64, FG0
	bn.mulqacc     	w1.0, w3.2, 0
	bn.mulqacc     	w1.1, w3.1, 0
	bn.mulqacc     	w1.2, w3.0, 0
	bn.mulqacc     	w1.0, w3.3, 64
	bn.mulqacc     	w1.1, w3.2, 64
	bn.mulqacc     	w1.2, w3.1, 64
	bn.mulqacc.so  	w10.U, w1.3, w3.0, 64, FG0
	bn.mulqacc     	w1.0, w2.0, 0
	bn.mulqacc     	w1.1, w3.3, 0
	bn.mulqacc     	w1.2, w3.2, 0
	bn.mulqacc     	w1.3, w3.1, 0
	bn.mulqacc     	w0.0, w3.0, 0
	bn.mulqacc     	w1.0, w2.1, 64
	bn.mulqacc     	w1.1, w2.0, 64
	bn.mulqacc     	w1.2, w3.3, 64
	bn.mulqacc     	w1.3, w3.2, 64
	bn.mulqacc     	w0.0, w3.1, 64
	bn.mulqacc.so  	w12.L, w0.1, w3.0, 64, FG0
	bn.mulqacc     	w1.1, w2.1, 0
	bn.mulqacc     	w1.2, w2.0, 0
	bn.mulqacc     	w1.3, w3.3, 0
	bn.mulqacc     	w0.0, w3.2, 0
	bn.mulqacc     	w0.1, w3.1, 0
	bn.mulqacc     	w1.2, w2.1, 64
	bn.mulqacc     	w1.3, w2.0, 64
	bn.mulqacc     	w0.0, w3.3, 64
	bn.mulqacc.so  	w12.U, w0.1, w3.2, 64, FG0
	bn.mulqacc     	w1.3, w2.1, 0
	bn.mulqacc     	w0.0, w2.0, 0
	bn.mulqacc     	w0.1, w3.3, 0
	bn.mulqacc     	w0.0, w2.1, 64
	bn.mulqacc.so  	w11.L, w0.1, w2.0, 64, FG0
	bn.mulqacc.so  	w11.U, w0.1, w2.1, 0, FG0
	bn.add         	w11, w11, w13, FG0
	ret            
