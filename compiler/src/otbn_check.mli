(* OTBN hardware-stack limit checks.

   The OTBN core has two fixed-size hardware stacks that the compiler must not
   overflow:
   - a loop stack of depth 8, used by the LOOP/LOOPI instructions that
     implement [repeat] loops; and
   - a call stack of depth 8, used by JAL/return to save return addresses.

   This pass rejects programs whose nesting of [repeat] loops or whose depth of
   (non-inlined) calls would exceed those limits.
   It is an overapproximation in some cases, so it may fail for valid programs.
   It is an underapproximation for system calls: it assumes that they don't make
   further calls or have loops. *)

val check_prog : ('info, 'asm) Prog.sprog -> unit
