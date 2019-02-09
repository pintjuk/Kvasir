open m0u_progTheory;
open Int;
open m0_decompLib;
open m0Theory;
open progSyntax;
open pairLib;
open pred_setSyntax;
open m0_progLib;
open m0_stepLib;
open wordsSyntax;
open progTheory;
open m0_progTheory;

 
val (code_th, code_defs) = m0_decompile "code"` 
  00c0
  1814
  5ce5
`;
(* to extend code pool with .word 0xabcdfff after the last instruction*)
(* by extending the code pool with  (p+6w, data_to_thumb2 (0xabcdefffw)) *)

(* Need the fact that extending code with .WORD is a subset  *)
val CODE_SUB = prove(``{(p,INL 192w); (p + 2w,INL 6164w); (p + 4w,INL 23781w)} SUBSET {(p,INL 192w); (p + 2w,INL 6164w); (p + 4w,INL 23781w); (p+6w, data_to_thumb2 (0xabcdefffw))}``,
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] );


(* Need the fact that .word is disjoint from the rest of the code *)

val CODE_DISJOINT_TAC = 
(REV_FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [PULL_EXISTS, m0_instr_def, data_to_thumb2_def]>>
REPEAT STRIP_TAC>>(
    REV_FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [PULL_EXISTS, m0_instr_def, data_to_thumb2_def]>>
    EVAL_TAC))


val CODE_DISJOINT = prove(`` (DISJOINT (m0_instr (p+6w, data_to_thumb2 (0xabcdefffw)))
                 (BIGUNION (IMAGE m0_instr {(p,INL 192w); (p + 2w,INL 6164w); (p + 4w,INL 23781w)} )))``, CODE_DISJOINT_TAC)

(* Now we should be able to extend the code using 

    (("prog", "SPEC_SUBSET_CODE"),
     ( [] ⊢ ∀x p c q. SPEC x p c q ⇒ ∀c'. c ⊆ c' ⇒ SPEC x p c' q, Thm)),

   AND we cane move data back and froth from conditions to code using:

    (("m0_prog", "MOVE_TO_M0_CODE_POOL"),
	( []
	⊢ ∀a w c p q.
		SPEC M0_MODEL
		(p * m0_MEM a ((7 >< 0) w) * m0_MEM (a + 1w) ((15 >< 8) w) *
		m0_MEM (a + 2w) ((23 >< 16) w) *
		m0_MEM (a + 3w) ((31 >< 24) w)) c
		(q * m0_MEM a ((7 >< 0) w) * m0_MEM (a + 1w) ((15 >< 8) w) *
		m0_MEM (a + 2w) ((23 >< 16) w) *
		m0_MEM (a + 3w) ((31 >< 24) w)) ⇔
		SPEC M0_MODEL
		(cond
		    (DISJOINT (m0_instr (a,data_to_thumb2 w))
			(BIGUNION (IMAGE m0_instr c))) * p)
		((a,data_to_thumb2 w) INSERT c) q, Thm)),


   But i suspect that the worklfow will be something like: 
   1) decompile 
   2) factor out the data in pre and post conditions
   3) use above stuff to move data into code
   4) check that data matches .word in content and address 
*)
