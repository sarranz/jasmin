Direct wide loads and stores with post-increment on ACC
(PLAN-acc-ld-incr.md). Each success file is compiled and printed without
assembler directives; each fail file must fail with the recorded error. The
instruction shapes (sequence, mnemonic, offset, the incremented register being
the address base, loop counts) and the error classes are what these tests pin;
register names, error columns and the numeric suffixes of variables in
register-allocation traces are incidental. Functions are printed in reverse
source order. When promoting a diff, check it against the comments in the test
files first.

  $ ../jasminc -arch acc -o out.s success/acc/intrinsic_bn_ld_inc.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  bn_ld_inc_loop:
  	bn.ld	w0, 0(x10++)
  	loop	x11, 2
  	bn.ld	w1, 0(x10++)
  	bn.xor	w0, w0, w1, FG0
  	ret
  bn_ld_inc_rename:
  	bn.ld	w0, 0(x10++)
  	ret
  bn_ld_inc:
  	bn.ld	w0, 0(x10++)
  	bn.ld	w1, 32(x10++)
  	bn.xor	w0, w0, w1, FG0
  	bn.ld	w1, -32(x10++)
  	bn.xor	w0, w0, w1, FG0
  	bn.ld	w1, 16352(x10++)
  	bn.xor	w0, w0, w1, FG0
  	bn.ld	w1, -16384(x10++)
  	bn.xor	w0, w0, w1, FG0
  	ret

  $ ../jasminc -arch acc -o out.s success/acc/intrinsic_bn_sd_inc.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  bn_sd_inc_loop:
  	loop	x11, 1
  	bn.sd	w0, 0(x10++)
  	ret
  bn_sd_inc_rename:
  	bn.sd	w0, 0(x10++)
  	ret
  bn_sd_inc:
  	bn.sd	w0, 0(x10++)
  	bn.sd	w0, 32(x10++)
  	bn.sd	w0, -32(x10++)
  	bn.sd	w0, 16352(x10++)
  	bn.sd	w0, -16384(x10++)
  	ret

  $ ../jasminc -arch acc -o out.s success/acc/bn_ld_sd_inc_copy.jazz && grep -v '^[[:space:]]*\.' out.s
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  bn_copy_inc:
  	loop	x12, 2
  	bn.ld	w0, 0(x11++)
  	bn.sd	w0, 0(x10++)
  	ret

The incremented register must be the base register of the address (checked by
the assembly printer, after register allocation).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_ld_inc_base_mismatch.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  pretty printing: the incremented register x11 must be the base register of the address 0(x10)
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_sd_inc_base_mismatch.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  pretty printing: the incremented register x11 must be the base register of the address 0(x10)
  [1]

The updated pointer and the input pointer share a register (same explicit
argument); when both stay live, register allocation rejects the program.

  $ ../jasminc -arch acc -o out.s fail/acc/bn_ld_inc_ptr_live.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_ld_inc_ptr_live.jazz", line 11 (4-45):
  compilation error:
  register allocation: conflicting variables “p.329” and “q.331” must be merged due to:
    at "fail/acc/bn_ld_inc_ptr_live.jazz", line 11 (4-45):
      x.330, q.331 = #BN.LD.INC([#aligned :u256 p.329], p.329);
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_sd_inc_ptr_live.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_sd_inc_ptr_live.jazz", line 10 (4-45):
  compilation error:
  register allocation: conflicting variables “p.327” and “q.329” must be merged due to:
    at "fail/acc/bn_sd_inc_ptr_live.jazz", line 10 (4-45):
      [#aligned :u256 p.327], q.329 = #BN.SD.INC(v.328, p.327);
  [1]

Arity: two inputs (address, pointer) and two outputs (value, updated pointer).

  $ ../jasminc -arch acc -o out.s fail/acc/bn_ld_inc_missing_ptr.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_ld_inc_missing_ptr.jazz", line 9 (4-42):
  typing error: invalid number of arguments, 1 provided instead of 2
  [1]

  $ ../jasminc -arch acc -o out.s fail/acc/bn_ld_inc_single_lval.jazz
  warning: support of the ACC architecture is VERY experimental. The loop instruction is not part of the verified compiler. The compiler does NOT check whether the loop stack overflow/underflows. The compiler does NOT check that memory accesses are aligned.
  "fail/acc/bn_ld_inc_single_lval.jazz", line 8 (4-42):
  typing error: invalid number of lvalues, 1 provided instead of 2
  [1]
