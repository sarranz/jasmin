Lowering of u256 logical shifts on ACC (PLAN-acc-lower-bn-shifts.md).
The success file is compiled and printed without assembler directives; each
fail file must fail with the recorded error. The expected blocks below were
written before the implementation: register names and the order of the
functions may differ, the instruction shapes (sequence, mnemonic, operand
order, immediate, flag group) must not. Promote only after checking every
diff against the comments in the test files.

  $ ../jasminc -arch acc -o out.s success/acc/bn_shift.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  shift_then_select:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w2, w2, w1 >> 8
  	bn.cmp	w0, w2, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  shr_keeps_source:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w2, w2, w0 >> 8
  	bn.add	w0, w0, w2, FG0
  	ret
  shr_then_shl:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 8
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 240
  	ret
  shl_wraps:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 248
  	ret
  shr_wraps_to_zero:
  	ret
  shr_0_merged:
  	ret
  shl_0_same:
  	ret
  shr_0_same:
  	ret
  shl_0_other:
  	bn.mov	w0, w1
  	ret
  shr_0_other:
  	bn.mov	w0, w1
  	ret
  shl_255:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 1
  	ret
  shr_255:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 255
  	ret
  shl_3:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 253
  	ret
  shr_3:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 3
  	ret
  shl_1:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 255
  	ret
  shr_1:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 1
  	ret
  shl_other:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w1, w2 >> 192
  	ret
  shr_other:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w1 >> 64
  	ret
  shl_in_place:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 240
  	ret
  shr_in_place:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 16
  	ret
  shl_8:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w0, w2 >> 248
  	ret
  shr_8:
  	bn.xor	w2, w2, w2, FG0
  	bn.rshi	w0, w2, w0 >> 8
  	ret

The amount of a wide shift must be a constant.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_shift_variable_amount.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_shift_variable_amount.jazz", line 5 (4-15):
  compilation error in function shift_variable_amount:
  lowering: invalid shift amount: i . The amount of a wide shift must be a constant.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_shift_left_variable_amount.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_shift_left_variable_amount.jazz", line 5 (4-15):
  compilation error in function shift_left_variable_amount:
  lowering: invalid shift amount: i . The amount of a wide shift must be a constant.
  [1]

Arithmetic wide shifts are not lowered (unchanged behavior).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_shift_arithmetic.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_shift_arithmetic.jazz", line 5 (4-16):
  compilation error in function shift_arithmetic:
  linearization: The following assignment remains:
  w0 = w0 >>256s (8u) 8
  Is there an instruction in the target architecture that can implement it?
  More information may be found online: https://jasmin-lang.readthedocs.io/en/stable/misc/faq.html#linearization
  [1]
