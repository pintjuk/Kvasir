open HolKernel Parse boolLib bossLib;
open m0_NITTheory
open uartTheory
open pairTheory;
open progTheory;
open m0u_progTheory;
open set_sepTheory;
open m0_NITTheory;
open m0_progTheory;
open uartTheory
open clockTheory;
open stateTheory m0_stepTheory;
open boolSimps;
open pred_setTheory;

val _ = new_theory "nit2bisim1";

(********************************************)
(*          No exceptions                   *)
(*                                          *)
(********************************************)

(* There will be no exceptions for t clock 
   cycles executing from a state constrained by P *)

val NEX_def = Define `
    NEX (P :(m0_component # m0_data -> bool) -> bool) t = ! s seq i.    
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               ((seq (SUC i)).count <= s.count+ t))==>   
	           ((seq i).count < (Next(seq i)).count) /\
                   ((Next (seq (i))).exception = NoException) `;


(* This is our strong non interference property
   After executing t clock cycles no information flow to or from the region can be observed
   in each step
*)
         
val NIT_def = Define`
NIT region(P :(m0_component # m0_data -> bool) -> bool)  t =   !s s' seq seq' i.   
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               m0_non_r_eq region s s' /\ 
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
               ((seq i).count <= s.count+t)) ==>   
                   m0_non_r_eq region (seq i) (seq' i) /\
                   m0_r_eq region s' (seq' i)`;
(* bisim *) 


val COSIM_def = Define ` COSIM P t = ! s s' seq seq' i.   
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    ~(((SND o FST) s').unpredictable)/\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count <= s.count + t) )==>   
	m0u_m0_non_r_eq uart_r (seq' i) (seq i) /\
	m0u_r_eq uart_r s' (seq' i)`;


val cosim_def = Define `cosim P c t = COSIM ((CODE_POOL m0_instr c) * P  ) t`;

val NEX_thm = Q.store_thm("NEX_thm",
    `! P t s seq i.
	NEX P t ==> (
	    SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
	    rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	    (seq (SUC i)).count <= s.count + t ==> 
                ((seq i).count < (Next(seq i)).count) /\ ((Next (seq i)) = (seq(SUC i))))`,
    REPEAT STRIP_TAC>>
    FULL_SIMP_TAC (std_ss++LET_ss) [NEX_def, PULL_FORALL]>>
    Q.PAT_X_ASSUM `!s seq i._` (MP_TAC o Q.SPECL [`s`,`seq`, `i`])>>
    FULL_SIMP_TAC (std_ss++LET_ss) [NEX_def, PULL_FORALL,rel_sequence_def, 
			    NEXT_REL_EQ, NextStateM0_def]>>
    METIS_TAC[]
);

val PRODUCT_STATE_lem = prove(``!s z_i. ?z_0. m0_non_r_eq uart_r s z_0 /\ m0_r_eq uart_r z_0 z_i``,
    REPEAT GEN_TAC>>
    EXISTS_TAC ``s with <|MEM := (\x. if (x IN uart_r) 
                                         then (z_i.MEM x)
                                         else (s.MEM x)) |>``>>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [m0Theory.m0_state_accfupds,
		m0_non_r_eq_def, m0_r_eq_def, mem_eq_def]
);

val eq_lem = prove(``!a b r.
    m0_non_r_eq r a  b /\ m0_r_eq r a b ==> (a=b)``,
			      
    REPEAT GEN_TAC>>
    Cases_on `a`>>Cases_on `b`>>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [m0Theory.m0_state_accfupds,
m0Theory.m0_state_accessors,m0_non_r_eq_def, m0_r_eq_def, mem_eq_def, m0Theory.m0_state_11]>>
    Cases_on  `x NOTIN r ` >> METIS_TAC[]
);

val   NIT_NIT_STEP_thm = store_thm("NIT_NIT_STEP_thm",
``  ! P t s seq i.
	NIT uart_r P t /\
	NEX P t ==> (
	SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
	rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	(seq (SUC i)).count <= s.count + t ==> NIT_STEP uart_r (seq i))``,
    REPEAT STRIP_TAC >>
    SIMP_TAC std_ss [NIT_STEP_thm]>>
    GEN_TAC>>
    rename1 `m0_non_r_eq uart_r (seq i) z_i`>>
    STRIP_TAC>>
    `?z_0. m0_non_r_eq uart_r s z_0 /\ m0_r_eq uart_r z_0 z_i` by( 
        METIS_TAC[PRODUCT_STATE_lem]
    )>>
    `?seq_z . rel_sequence (NEXT_REL $= NextStateM0) seq_z z_0` by(
        METIS_TAC[SEQUENCE_EXISTS_THM]
    )>>
 
    `(seq i).count ≤ s.count + t` by(
	METIS_TAC[NEX_thm,
	    DECIDE ``((a:num) < (b:num) /\ b <= (c:num)) ==>( a <= c)``])>>

    `z_i = seq_z i ` by (
	Q.PAT_ASSUM `NIT uart_r P t` (MP_TAC o 
				  Q.SPECL [`s`, `z_0`, `seq`, `seq_z`, `i`] o
                                  REWRITE_RULE [NIT_def])>>
	METIS_TAC[m0_r_eq_trans_thm, m0_r_eq_antisym_thm,
                  m0_non_r_eq_trans_thm, m0_non_r_eq_antisym_thm,
                  eq_lem])>>
    
    Q.PAT_ASSUM `NIT uart_r P t` (MP_TAC o 
	   			  Q.SPECL [`s`, `z_0`, `seq`, `seq_z`, `SUC i`] o
                                  REWRITE_RULE [NIT_def])>>
    ASM_SIMP_TAC std_ss []>>
    STRIP_TAC>>

    `(seq(SUC i) = Next (seq(i)))` by  (METIS_TAC[NEX_thm])>>

   `(seq_z(SUC i) = Next (seq_z(i)))` by(
        (* a step must have taken place between (seq_z i) and i+1 
           since the count between them has increesed *) 
	`(seq_z(i)).count < (seq_z(SUC i)).count ` by
	    METIS_TAC[NEX_thm,  m0_non_r_eq_def]>>
	Q.PAT_X_ASSUM `rel_sequence (NEXT_REL $= NextStateM0) seq_z s_0` 
	    (MP_TAC o Q.SPEC `i` o 
	    SIMP_RULE (std_ss++LET_ss)[
		rel_sequence_def, PULL_EXISTS,NEXT_REL_EQ,
		NextStateM0_def, PULL_FORALL])>>
         IF_CASES_TAC >-  (METIS_TAC[] )>>
	 STRIP_TAC >> FULL_SIMP_TAC arith_ss[]
    )>>
    
    METIS_TAC[m0_r_eq_trans_thm,m0_r_eq_antisym_thm]
);
 
val LEM = prove(
    ``!(a:((m0_state # uart_state) # word32 list # word32 list)) 
       (b:((m0_state # uart_state) # word32 list # word32 list)) region.
	    m0u_r_eq region a b ==> ((SND (FST a)) = (SND (FST b)))``, 
    Cases_on `a`>> Cases_on `b`>> Cases_on `q`>>
    Cases_on `q'`>> Cases_on `r`>> Cases_on `r'`>>
    SIMP_TAC std_ss [m0u_r_eq_def]
);
val LEM1 = prove(
    ``!a b region. (m0u_m0_non_r_eq  region a b) ==> 
	((FST (FST a)).count =  b.count)/\
	((FST (FST a)).exception =  b.exception)``, 
    Cases_on `a`>> Cases_on `q`>> Cases_on `r`>>
    SIMP_TAC std_ss [m0u_m0_non_r_eq_def, m0_non_r_eq_def]
);

val NIT_COSIM_thm = Q.store_thm ("NIT_COSIM_thm", 
    `!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM P t)`, 
    SIMP_TAC std_ss [ COSIM_def, PULL_FORALL]>>
    REPEAT GEN_TAC>>
    Induct_on `i`>-(
        ASM_SIMP_TAC std_ss [rel_sequence_def, m0u_r_eq_refl_thm]
    )>>
    STRIP_TAC>>STRIP_TAC>>
    `(seq i).count ≤ s.count + t` by(
	METIS_TAC[NEX_thm,
	    DECIDE ``((a:num) < (b:num) /\ b <= (c:num)) ==>( a <= c)``])>>
    FULL_SIMP_TAC std_ss []>>
    (MP_TAC o Q.SPECL [`P`,`t`,`s`,`seq`, `i`]) NIT_NIT_STEP_thm>>
    ASM_SIMP_TAC std_ss[]>>
    STRIP_TAC>>
    `(seq(SUC i) = Next (seq(i)))` by  (METIS_TAC[NEX_thm])>>
    (MP_TAC o Q.SPECL [`seq (i:num)`, `seq' (i:num)`]) AXI>>
    ASM_SIMP_TAC std_ss[]>>
    STRIP_TAC>>
    `seq' (SUC i) = m0u_Next (seq' i)` by (
	`(Next (seq i)).exception = NoException` by (
	    Q.PAT_X_ASSUM `NIX P t` ( 
                MP_TAC o Q.SPECL [`s`, `seq`, `i`] o
		REWRITE_RULE [NEX_def])>>
	    FULL_SIMP_TAC std_ss []
	)>>
	` m0u_r_eq uart_r s' (m0u_Next (seq' i))` by(
	    METIS_TAC [m0u_r_eq_trans_thm, m0u_r_eq_antisym_thm]
        )>>
	Q.PAT_X_ASSUM `rel_sequence (NEXT_REL $= NextStateM0U) seq' s'` (MP_TAC o
	    SPEC ``i:num`` o
	    CONJUNCT2 o
	    REWRITE_RULE [PULL_FORALL,rel_sequence_def, 
                          NEXT_REL_EQ, NextStateM0U_def]
        )>>
	ASM_SIMP_TAC (std_ss++LET_ss) []>>
	METIS_TAC[NextStateM0U_def, LEM, LEM1]
    )>>
    METIS_TAC [m0u_r_eq_trans_thm,  m0u_r_eq_antisym_thm]
);

val _ = export_theory();
