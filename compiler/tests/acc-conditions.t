Lowering of u256 comparisons on ACC (PLAN-acc-lower-bn-comparisons.md).
Each success file is compiled and printed without assembler directives; each
fail file must fail with the recorded error. The expected blocks below were
written before the implementation: register names may differ, the instruction
shapes (sequence, mnemonic, flag group, flag letter, source order) must not.
Promote only after checking every diff against the comments in the test files.

  $ ../jasminc -arch acc -o out.s success/acc/bn_cmp_ternary.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  keeps_fg0:
  	bn.mov	w2, w1
  	bn.cmp	w0, w1, FG0
  	bn.cmp	w0, w1, FG1
  	bn.sel	w2, w2, w0, FG1.C
  	bn.sel	w0, w2, w0, FG0.C
  	ret
  twice:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w2, w0, w2, FG1.C
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w2, FG1.Z
  	ret
  not_leu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  not_not_ltu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  not_eq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  ltu_reversed:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  three:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w2, FG1.C
  	ret
  gtu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  leu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  geu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  ltu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  neq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  eq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret

  $ ../jasminc -arch acc -o out.s success/acc/bn_cmp_bool.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  bool_sequential:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w2, w0, w2, FG1.C
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w2, FG1.Z
  	ret
  bool_used_twice:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w1, w0, w1, FG1.C
  	bn.sel	w0, w0, w2, FG1.C
  	bn.xor	w0, w1, w0, FG0
  	ret
  bool_negated_use:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  bool_negated_rhs:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  bool_declared_then_assigned:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  bool_gtu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  bool_leu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  bool_geu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  bool_ltu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  bool_neq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  bool_eq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret

  $ ../jasminc -arch acc -o out.s success/acc/bn_cmp_intrinsic.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  sel_flag_unchanged:
  	bn.cmp	w0, w1, FG0
  	bn.sel	w0, w0, w1, FG0.C
  	ret
  sel_three:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w2, FG1.Z
  	ret
  sel_not_geu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  sel_gtu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  sel_leu:
  	bn.cmp	w1, w0, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  sel_geu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  sel_ltu:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  sel_neq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  sel_eq:
  	bn.cmp	w0, w1, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret

  $ ../jasminc -arch acc -o out.s success/acc/bn_cmp_shift.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  sel_shift:
  	bn.cmp	w0, w1 >> 8, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret
  bool_shift:
  	bn.cmp	w0, w1 << 8, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  shift_zero:
  	bn.cmp	w0, w1 << 0, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret
  gtu_shift_left:
  	bn.cmp	w1, w0 >> 16, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  leu_shift_left:
  	bn.cmp	w1, w0 << 8, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  geu_shift_right:
  	bn.cmp	w0, w1 << 248, FG1
  	bn.sel	w0, w1, w0, FG1.C
  	ret
  ltu_shift_right:
  	bn.cmp	w0, w1 >> 8, FG1
  	bn.sel	w0, w0, w1, FG1.C
  	ret
  neq_shift_left:
  	bn.cmp	w1, w0 << 16, FG1
  	bn.sel	w0, w1, w0, FG1.Z
  	ret
  eq_shift_right:
  	bn.cmp	w0, w1 << 8, FG1
  	bn.sel	w0, w0, w1, FG1.Z
  	ret

Signed wide comparisons are a user error in lowering.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_signed_ternary.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_signed_ternary.jazz", line 5 (4-22):
  compilation error in function signed_ternary:
  lowering: signed comparison of wide registers is not supported (ACC has no overflow flag): a <s b . Use the signed labels of #BN_CMP if the difference cannot overflow.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_signed_bool.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_signed_bool.jazz", line 5 (4-25):
  compilation error in function signed_bool:
  lowering: signed comparison of wide registers is not supported (ACC has no overflow flag): a >=s b . Use the signed labels of #BN_CMP if the difference cannot overflow.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_signed_intrinsic.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_signed_intrinsic.jazz", line 6 (4-34):
  compilation error in function signed_intrinsic:
  lowering: signed comparison of wide registers is not supported (ACC has no overflow flag): a <=s b . Use the signed labels of #BN_CMP if the difference cannot overflow.
  [1]

A shifted operand must end up as the second BN.CMP operand.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_shift_side_ltu.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_shift_side_ltu.jazz", line 5 (4-29):
  compilation error in function shift_side_ltu:
  lowering: shifted operand on the wrong side of the comparison: a <<256u (8u) 8 <u b . Only the second BN.CMP operand can be shifted: the right operand of <u and >=u, the left operand of <=u and >u, either operand of == and !=.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_shift_side_leu.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_shift_side_leu.jazz", line 5 (4-30):
  compilation error in function shift_side_leu:
  lowering: shifted operand on the wrong side of the comparison: a <=u b <<256u (8u) 8 . Only the second BN.CMP operand can be shifted: the right operand of <u and >=u, the left operand of <=u and >u, either operand of == and !=.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_shift_both.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_shift_both.jazz", line 5 (4-37):
  compilation error in function shift_both:
  lowering: shifted operand on the wrong side of the comparison: a <<256u (8u) 8 ==256u b <<256u (8u) 16 . Only the second BN.CMP operand can be shifted: the right operand of <u and >=u, the left operand of <=u and >u, either operand of == and !=.
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_shift_amount.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_shift_amount.jazz", line 4 (4-29):
  compilation error in function shift_amount:
  lowering: invalid shift amount: 4 . Must be in the range [0, 31] or masked with 0x1f.
  [1]

Composite labels of #BN_CMP as a BN.SEL condition (unchanged user error).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_composite_label.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_composite_label.jazz", line 8 (4-17):
  compilation error in function composite_label:
  asmgen: not able to compile the condition CF0 || ZF0
          the BN.SEL condition must be a single flag or its negation; the composite labels <=u, >u, <=s, >s are not supported here, use the opposite label or swap the compared operands
  [1]

Two lowered comparisons before the first bool is used: the shared fresh flags
are overwritten, the first bool is not substituted and cannot be allocated.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_bool_interleaved.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  compilation error:
  register allocation: variables { lt.349 } remain unallocated
  [1]

A user FG1 flag live across a lowered compare conflicts in register allocation.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_fg1_conflict.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_fg1_conflict.jazz", line 8 (4-23):
  compilation error:
  register allocation: variable __cf1__.344 must be allocated to register CF1 due to architectural constraints; this register already holds conflicting variable: cf.340
  [1]

32-bit comparisons are not lowered (unchanged behavior).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_u32_bool.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  compilation error:
  register allocation: variables { c.331 } remain unallocated
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_u32_ternary.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_u32_ternary.jazz", line 5 (4-22):
  internal compilation error in function u32_ternary:
    lowering: invalid wsize
  Please report at https://github.com/jasmin-lang/jasmin/issues
  [1]

Wide comparisons cannot be branch conditions (unchanged behavior).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_cmp_if_wide.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_cmp_if_wide.jazz", line 6 (4) to line 8 (5):
  compilation error in function if_wide:
  asmgen: not able to compile the condition w0 ==256u w1
          Can't assemble condition.
  [1]
