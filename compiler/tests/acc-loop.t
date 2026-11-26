  $ ../jasminc -arch acc success/acc/loop.jazz -o out.s
  warning: support of the ACC architecture is VERY experimental. The compiler does NOT check that memory accesses are aligned.
  $ cat out.s
  	.global	la_last_in_loop
  	.global	nested_with_cond
  	.global	while_in_repeat
  	.global	reg_count_cond_at_end
  	.global	two_inner_with_tail
  	.global	two_inner_second_last
  	.global	triple_nested
  	.global	nested_inner_not_last
  	.global	nested_inner_last
  	.global	if_only_at_end
  	.global	cond_not_at_end
  	.global	cond_at_end
  	.global	empty
  	.global	main
  	.type	la_last_in_loop, %function
  la_last_in_loop:
  	li  	x3, 0
  	la  	x4, glob_data+0
  	beq 	x10, x0, Lla_last_in_loop$2
  	loop	x10, 4
  Lla_last_in_loop$1:
  	lw  	x4, 0(x4)
  	add 	x3, x3, x4
  	la  	x4, glob_data+0
  Lla_last_in_loop$2:
  	addi	x10, x3, 0
  	ret
  	.type	nested_with_cond, %function
  nested_with_cond:
  	loopi	3, 7
  Lnested_with_cond$1:
  	loopi	5, 5
  Lnested_with_cond$2:
  	beq 	x10, x0, Lnested_with_cond$3
  	addi	x10, x10, 2
  	beq 	x0, x0, Lnested_with_cond$4
  Lnested_with_cond$3:
  	addi	x10, x10, 1
  Lnested_with_cond$4:
  	nop
  	nop
  	ret
  	.type	while_in_repeat, %function
  while_in_repeat:
  	loopi	4, 4
  Lwhile_in_repeat$1:
  	beq 	x0, x0, Lwhile_in_repeat$2
  Lwhile_in_repeat$3:
  	addi	x10, x10, 1
  Lwhile_in_repeat$2:
  	bne 	x10, x11, Lwhile_in_repeat$3
  	nop
  	ret
  	.type	reg_count_cond_at_end, %function
  reg_count_cond_at_end:
  	beq 	x11, x0, Lreg_count_cond_at_end$2
  	loop	x11, 5
  Lreg_count_cond_at_end$1:
  	beq 	x10, x0, Lreg_count_cond_at_end$3
  	addi	x10, x10, 2
  	beq 	x0, x0, Lreg_count_cond_at_end$4
  Lreg_count_cond_at_end$3:
  	addi	x10, x10, 1
  Lreg_count_cond_at_end$4:
  	nop
  Lreg_count_cond_at_end$2:
  	ret
  	.type	two_inner_with_tail, %function
  two_inner_with_tail:
  	loopi	4, 5
  Ltwo_inner_with_tail$1:
  	loopi	2, 1
  Ltwo_inner_with_tail$3:
  	addi	x10, x10, 1
  	loopi	3, 1
  Ltwo_inner_with_tail$2:
  	addi	x10, x10, 2
  	addi	x10, x10, 4
  	ret
  	.type	two_inner_second_last, %function
  two_inner_second_last:
  	loopi	4, 5
  Ltwo_inner_second_last$1:
  	loopi	2, 1
  Ltwo_inner_second_last$3:
  	addi	x10, x10, 1
  	loopi	3, 1
  Ltwo_inner_second_last$2:
  	addi	x10, x10, 2
  	nop
  	ret
  	.type	triple_nested, %function
  triple_nested:
  	loopi	2, 5
  Ltriple_nested$1:
  	loopi	3, 3
  Ltriple_nested$2:
  	loopi	4, 1
  Ltriple_nested$3:
  	addi	x10, x10, 1
  	nop
  	nop
  	ret
  	.type	nested_inner_not_last, %function
  nested_inner_not_last:
  	loopi	4, 3
  Lnested_inner_not_last$1:
  	loopi	3, 1
  Lnested_inner_not_last$2:
  	addi	x10, x10, 1
  	addi	x10, x10, 1
  	ret
  	.type	nested_inner_last, %function
  nested_inner_last:
  	loopi	4, 3
  Lnested_inner_last$1:
  	loopi	3, 1
  Lnested_inner_last$2:
  	addi	x10, x10, 1
  	nop
  	ret
  	.type	if_only_at_end, %function
  if_only_at_end:
  	loopi	4, 3
  Lif_only_at_end$1:
  	beq 	x10, x0, Lif_only_at_end$2
  	addi	x10, x10, 1
  Lif_only_at_end$2:
  	nop
  	ret
  	.type	cond_not_at_end, %function
  cond_not_at_end:
  	loopi	4, 5
  Lcond_not_at_end$1:
  	beq 	x10, x0, Lcond_not_at_end$2
  	addi	x10, x10, 2
  	beq 	x0, x0, Lcond_not_at_end$3
  Lcond_not_at_end$2:
  	addi	x10, x10, 1
  Lcond_not_at_end$3:
  	addi	x10, x10, 3
  	ret
  	.type	cond_at_end, %function
  cond_at_end:
  	loopi	4, 5
  Lcond_at_end$1:
  	beq 	x10, x0, Lcond_at_end$2
  	addi	x10, x10, 2
  	beq 	x0, x0, Lcond_at_end$3
  Lcond_at_end$2:
  	addi	x10, x10, 1
  Lcond_at_end$3:
  	nop
  	ret
  	.type	empty, %function
  empty:
  	li  	x10, 0
  	loopi	4, 1
  Lempty$10:
  	nop
  	loopi	43, 1
  Lempty$9:
  	nop
  	beq 	x10, x0, Lempty$8
  	loop	x10, 1
  Lempty$7:
  	nop
  Lempty$8:
  	loopi	47, 1
  Lempty$6:
  	nop
  	loopi	1, 1
  Lempty$5:
  	nop
  	li  	x10, 4
  	beq 	x0, x0, Lempty$1
  Lempty$2:
  	beq 	x10, x0, Lempty$4
  	loop	x10, 1
  Lempty$3:
  	nop
  Lempty$4:
  	addi	x10, x10, -1
  Lempty$1:
  	bne 	x10, x0, Lempty$2
  	ret
  	.type	main, %function
  main:
  	li  	x10, 0
  	loopi	4, 2
  Lmain$10:
  	jal 	x1, Lbody$1
  Lmain$11:
  	nop
  	loopi	43, 2
  Lmain$8:
  	jal 	x1, Lbody$1
  Lmain$9:
  	nop
  	beq 	x10, x0, Lmain$6
  	loop	x10, 2
  Lmain$5:
  	jal 	x1, Lbody$1
  Lmain$7:
  	nop
  Lmain$6:
  	loopi	47, 2
  Lmain$3:
  	jal 	x1, Lbody$1
  Lmain$4:
  	nop
  	loopi	1, 2
  Lmain$1:
  	jal 	x1, Lbody$1
  Lmain$2:
  	nop
  	ret
  Lbody$1:
  	addi	x10, x10, 1
  	ret
  	.data
  	.p2align	5
  glob_data:
  G$g:
  	.byte	  1,   0,   0,   0,   2,   0,   0,   0,   3,   0,   0,   0,   4,   0,   0,   0
  	.ident	"Jasmin Compiler @VERSION@"
  	.section	".note.GNU-stack", "", %progbits

  $ ../jasminc -arch acc success/acc/nested_loops_across_call.jazz -o out.s
  warning: support of the ACC architecture is VERY experimental. The compiler does NOT check that memory accesses are aligned.
  $ cat out.s
  	.global	main
  	.type	main, %function
  main:
  	loopi	2, 8
  Lmain$1:
  	loopi	2, 6
  Lmain$2:
  	loopi	2, 4
  Lmain$3:
  	loopi	2, 2
  Lmain$4:
  	jal 	x1, Linner$1
  Lmain$5:
  	nop
  	nop
  	nop
  	nop
  	ret
  Linner$1:
  	loopi	2, 7
  Linner$2:
  	loopi	2, 5
  Linner$3:
  	loopi	2, 3
  Linner$4:
  	loopi	2, 1
  Linner$5:
  	addi	x10, x10, 1
  	nop
  	nop
  	nop
  	ret
  	.ident	"Jasmin Compiler @VERSION@"
  	.section	".note.GNU-stack", "", %progbits

  $ ../jasminc -arch acc -plinear success/acc/reg_count_pin.jazz
  warning: support of the ACC architecture is VERY experimental. The compiler does NOT check that memory accesses are aligned.
  /* -------------------------------------------------------------------- */
  /* After linearization */
  
  
  
  (* maximal stack usage: 0, alignment = u8 *)
  fn reg_count_pin (reg u32 x10, reg u32 x11) -> (u32) {
    If x11 ==32u (32u) 0 goto 2;
    repeat_begin x11 1;
    Label 1;
    x10 = ADDI(x10, (32u) 1);
    repeat_end 1;
    Label 2
    return x10
  }
  
  
