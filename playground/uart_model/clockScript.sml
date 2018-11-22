(********************************************)
(*   properties of next and rel_sequances   *)
(********************************************)

open HolKernel Parse boolLib bossLib;
open m0Theory progTheory m0_progTheory stateTheory m0_stepTheory;
open boolSimps;
val _ = new_theory "clock"

(* next is strictly monotonically increasing in clock cycles *)
		  
val  NEXT_MONO = Q.store_thm("NEXT_MONO",
`!s. s.count <= (Next s).count`,
cheat
);


(*
execution sequences are strictly monotonically increasing
in clock cycles
 *)
val SEQ_MONO1 = Q.prove(
`!s i seq. rel_sequence (NEXT_REL $= NextStateM0) seq s ==>  (seq i).count <= (seq (i+1)).count`,
    SIMP_TAC (std_ss++LET_ss) [rel_sequence_def,NEXT_REL_def, PULL_EXISTS, PULL_FORALL, NextStateM0_def, DECIDE ``SUC i= i+1``]>>
    REPEAT STRIP_TAC>>
    Q.PAT_X_ASSUM `!n:num._` ( MP_TAC o (Q.SPEC `i:num`))>>
    IF_CASES_TAC>>(
        STRIP_TAC>>
        Q.PAT_X_ASSUM `x:m0_state=_` (( SIMP_TAC std_ss) o (fn x => x::[]) o GSYM)
    )>>
    MP_TAC( SPEC ``(seq (i:num)):m0_state`` NEXT_MONO ) >>
    DECIDE_TAC
);

val SEQ_MONO2 = Q.prove(
`!s  i d seq. rel_sequence (NEXT_REL $= NextStateM0) seq s ==>  (seq i).count <= (seq (i+d)).count`,
    REPEAT STRIP_TAC>>
    Induct_on `d`>-(
        SIMP_TAC arith_ss [] )>>
    (MP_TAC o Q.SPECL [`s`, `i+d`, `seq`] ) SEQ_MONO1>>
    FULL_SIMP_TAC arith_ss [DECIDE ``i + SUC d=i+ d+1``]
);


val SEQ_MONO_A = Q.store_thm("SEQ_MONO_A",
`!s a b seq. rel_sequence (NEXT_REL $= NextStateM0) seq s /\  (seq a).count < (seq b).count ==> a <= b `,
    REPEAT STRIP_TAC>>
    Cases_on `a<=b`>>(
	ASM_SIMP_TAC std_ss [])>>
    MP_TAC (Q.SPECL [`s`, `b`, `a-b`, `seq`] SEQ_MONO2)>>
    FULL_SIMP_TAC arith_ss []
);

val SEQ_MONO_B = Q.store_thm("SEQ_MONO_B",
`!s a b seq. rel_sequence (NEXT_REL $= NextStateM0) seq s /\ a <= b ==> (seq a).count <= (seq b).count `,
    REPEAT STRIP_TAC>>
    MP_TAC (Q.SPECL [`s`, `a`, `b-a`, `seq`] SEQ_MONO2)>>
    FULL_SIMP_TAC arith_ss []
);
(*
val SEQ_UNIQUE1 = Q.prove(
`!s i seq. rel_sequence (NEXT_REL $= NextStateM0) seq s /\ ( (seq i).count = (seq (i+1)).count)  ==>
(seq i = seq (i+1))
 `,
    SIMP_TAC (std_ss++LET_ss) [
         rel_sequence_def,NEXT_REL_def,
         PULL_EXISTS, PULL_FORALL, 
         NextStateM0_def, DECIDE ``SUC i= i+1``]>>
    REPEAT STRIP_TAC>>
    Q.PAT_X_ASSUM `!n:num._` ( MP_TAC o (Q.SPEC `i:num`))>>
    IF_CASES_TAC>>(
        STRIP_TAC>>
        ASM_SIMP_TAC std_ss []
    )>>
        MP_TAC( SPEC ``(seq (i:num)):m0_state`` NEXT_MONO ) >>	
        ASM_SIMP_TAC std_ss []
);

val SEQ_MONO2 = Q.prove(
`!s  i d seq. rel_sequence (NEXT_REL $= NextStateM0) seq s /\ ( (seq i).count = (seq (i+d)).count) ==>( (seq i) = (seq (i+d)))`,
    REPEAT STRIP_TAC>>
    Induct_on `d`>-(
        SIMP_TAC arith_ss [] )>>
    (MP_TAC o Q.SPECL [`s`, `i`, `i+d`, `seq`] ) SEQ_MONO_B>>
    (MP_TAC o Q.SPECL [`s`, `i+d`, `i+d+1`, `seq`] ) SEQ_MONO_B>>
    (MP_TAC o Q.SPECL [`s`, `i+d`, `seq`] ) SEQ_UNIQUE1>>
    FULL_SIMP_TAC arith_ss [DECIDE ``i + SUC d=(i+ d)+1``]
);

val SEQ_MONO = Q.store_thm("SEQ_UNIQUE",
`!s a b seq. rel_sequence (NEXT_REL $= NextStateM0) seq s /\ ( (seq a).count = (seq b).count) ==> ((seq a) = (seq b)) `,
    REPEAT STRIP_TAC>>
    Cases_on `a=b`>>(
	ASM_SIMP_TAC std_ss [])>>
    Cases_on `a<b`>|[
	MP_TAC (Q.SPECL [`s`, `a`, `b-a`, `seq`] SEQ_MONO2)>>
	`a+(b-a)=b` by DECIDE_TAC>>
	ASM_SIMP_TAC std_ss[],
  
	MP_TAC (Q.SPECL [`s`, `b`, `a-b`, `seq`] SEQ_MONO2)>>
	`b+(a-b)=a` by DECIDE_TAC>>
	ASM_SIMP_TAC std_ss[]
    ]
);

*)
val _ = export_theory();
