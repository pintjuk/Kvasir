(*
         loadPath := ("../uart"::(!loadPath));
         loadPath := ("../prog"::(!loadPath));
         loadPath := ("../clock"::(!loadPath));
 *)

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




val _ = new_theory "nit2bisim2";


fun rm_assum pat = Q.PAT_X_ASSUM pat (fn x => ALL_TAC );
(********************************************)
(*          No exceptions                   *)
(*                                          *)
(********************************************)


val SEQ_MONO_LEM = Q.prove( `!seq s i t.
    (rel_sequence (NEXT_REL $= NextStateM0) seq s)/\
    ((seq (SUC i)).count < s.count + t)==> ((seq i).count < s.count + t)`,
    REPEAT GEN_TAC>>
    (MP_TAC o Q.SPECL[`s`,`i`,`SUC i`,`seq`] ) SEQ_MONO_B>>
    ASM_SIMP_TAC std_ss []>>
    METIS_TAC [ DECIDE ``( x:num <= y:num /\ y < z:num ) ==> (x < z) ``]
);
(* will be no exceptions for t clock 
   cycles executing from a state constrained by P *)

val NEX_def = Define `
    NEX (P :(m0_component # m0_data -> bool) -> bool) t = ! s seq i.    
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               ((seq (i)).count < s.count+ t))==>   
	           ((seq i).count < (Next(seq i)).count) /\
                   ((Next (seq (i))).exception = NoException) `;

val NEX_thm = Q.store_thm("NEX_thm",
    `! P t s seq i. 
        (NEX P t) ==> 
            SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
            rel_sequence (NEXT_REL $= NextStateM0) seq s /\
            (seq (i)).count < s.count + t ==>
                ((seq i).count < (Next(seq i)).count) /\ ((Next (seq i)) = (seq(SUC i)))`,
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    REPEAT GEN_TAC>>
    Induct_on `i` >- (
        STRIP_TAC>>
        `(seq 0).count < (Next (seq 0)).count ∧
        ((Next (seq 0)).exception = NoException)` by METIS_TAC[NEX_def]>>
        FULL_SIMP_TAC std_ss [NEX_def, rel_sequence_def, NEXT_REL_def, NextStateM0_def, LET_DEF]>>
        `Next (seq 0) = seq (SUC 0)` by METIS_TAC[]>>
        REV_FULL_SIMP_TAC std_ss []
    )>>
    STRIP_TAC>>
    `(seq (SUC i)).count < (Next (seq (SUC i))).count ∧
    ((Next (seq (SUC i))).exception = NoException)` by METIS_TAC[NEX_def, SEQ_MONO_LEM]>>
    FULL_SIMP_TAC std_ss [NEX_def, rel_sequence_def, NEXT_REL_def, NextStateM0_def, LET_DEF]>>
    METIS_TAC[]
);

val NEX_VERI_0_thm= Q.store_thm("NEX_VERI_0_thm",
`!P. NEX P 0`,
    fs[NEX_def]>>
    REPEAT strip_tac>>
    (`(s).count ≤ (seq i).count` by
        METIS_TAC[SEQ_MONO_B, DECIDE ``0n<=i``, 
                  rel_sequence_def, NEXT_REL_def,
                  NextStateM0_def]
        )>>
    fs[]
);

val VC_def = Define`
VC region(P :(m0_component # m0_data -> bool) -> bool)  t =   !s s' seq seq' i.   
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               m0_non_r_eq region s s' /\ 
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
               ((seq i).count < s.count+t)) ==>   
                   m0_non_r_eq region (seq (SUC i)) (seq' (SUC i)) /\
                   m0_r_eq region (seq' 0) (seq' (SUC i))
`;

(* This is our strong non interference property
   After executing t clock cycles no information flow to or from the region can be observed
   in each step
*)

val eq_lem = prove(``!a b r.
    m0_non_r_eq r a  b /\ m0_r_eq r a b ==> (a=b)``,
    REPEAT GEN_TAC>>
    Cases_on `a`>>Cases_on `b`>>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [m0Theory.m0_state_accfupds,
            m0Theory.m0_state_accessors,m0_non_r_eq_def, m0_r_eq_def, mem_eq_def, m0Theory.m0_state_11]>>
    Cases_on  `x NOTIN r ` >> METIS_TAC[]
);

val PRODUCT_STATE_lem = prove(``!s z_i. ?z_0. m0_non_r_eq uart_r s z_0 /\ m0_r_eq uart_r z_0 z_i``,
    REPEAT GEN_TAC>>
    EXISTS_TAC ``s with <|MEM := (\x. if (x IN uart_r) 
                                         then (z_i.MEM x)
                                         else (s.MEM x)) |>``>>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [m0Theory.m0_state_accfupds,
		m0_non_r_eq_def, m0_r_eq_def, mem_eq_def]
);

val VC_WEAKEN_lem = prove(
    ``! P t t' uart_r.
         (VC uart_r P t) /\ 
         (t' <= t)  
          ==> VC uart_r P t'``,
    SIMP_TAC std_ss [VC_def]>>
    REPEAT STRIP_TAC>>
    `(seq i).count < s.count + t` by DECIDE_TAC>>
    METIS_TAC []
);

val NEX_WEAKEN_lem = prove(
    ``! P t t' uart_r.
         (NEX P t) /\ 
         (t' <= t)  
          ==> NEX P t'``,
    SIMP_TAC std_ss [NEX_def]>>
    REPEAT STRIP_TAC>>
    `(seq i).count < s.count + t` by DECIDE_TAC>>
    METIS_TAC []
);

val m0_non_r_eq_lem = prove(
    ``!a b region. (m0_non_r_eq  region a b) ==>
        (a.count =  b.count)/\
        (a.exception =  b.exception)``,
    
    SIMP_TAC std_ss [m0_non_r_eq_def, m0_non_r_eq_def]
);

val EXISTS_PRE_STATE_lem = prove(``
! P t seq seq' (i:num) (s:m0_state) (s':m0_state) region .
	VC region P t /\
	NEX P t /\
	  SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
          m0_non_r_eq region s s' /\ 
	  rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	  rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
          (seq i).count > (seq 0).count/\
          ((seq i).count = s.count+t) ==>   
             ?i'.( ((seq i' ).count < (s.count +t))
                    /\ ((seq (SUC i'))=(seq i)) 
                    /\ ((seq' (SUC i'))=(seq' i)))
``,

    REPEAT STRIP_TAC>> 
    `
            ∃i'. (seq i').count < (seq i).count ∧ (seq (i' + 1) = seq i)

    ` by METIS_TAC[ SEQ_EXISTS_PREV_STATE_thm ]>>
    
    qexists_tac  `i'`>>
    rfs [ DECIDE``i' + 1 = SUC i' ``]>>
    (* parallel run has same prestate lemma *)
           Cases_on  `i'>=i`>- (
                `(seq i).count ≤ (seq i').count` by  
                        METIS_TAC[SEQ_MONO_B, DECIDE ``  (i':num >= i ) <=> (i<= i') `` ]>>
                `(seq i').count <  (seq i).count` by asm_simp_tac arith_ss[]>>
                full_simp_tac arith_ss[]
           )>>
           Cases_on  `i'+1=i`>-( 
                fs [DECIDE ``i'+1=SUC i'``]
           )>>
           
(*           `i'< i-1` by DECIDE_TAC>>
           `i'<= i-1` by DECIDE_TAC>>
           `i' + 2<= i` by DECIDE_TAC>>
           `(seq i').count ≤ (seq (i-1)).count` by METIS_TAC[ SEQ_MONO_B]
           `(seq (i'+2)).count ≤ (seq (i)).count` by METIS_TAC[ SEQ_MONO_B]
           `   
                (seq (i'+1)).count < (Next (seq (i'+ 1))).count ∧
                ((Next (seq (i'+1))).exception = NoException)
           `by METIS_TAC[NEX_def, DECIDE  ``s.count + t=  t+s.count``]

            `(Next (seq' i')).exception = NoException ` by METIS_TAC[m0_non_r_eq_lem] 

*)
    `
           seq' (SUC i') = seq' i
           
    ` by cheat>>
    fs[]
);



val FINAL_STATE_EQ_lem = prove(
``! P t seq seq' (i:num) (s:m0_state) (s':m0_state) region .
	VC region P t /\
	NEX P t /\
               SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
               m0_non_r_eq region s s' /\ 
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
               ((seq i).count = s.count+t) ==>   
                   m0_non_r_eq region (seq i) (seq' i) /\
                   m0_r_eq region (seq' 0) (seq' i)
``,
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    (* take care of the case of t=0 *)
    Tactical.REVERSE ( Cases_on `t>0` ) >- (
        `t=0` by DECIDE_TAC>>
         rm_assum  `¬(t > 0)`>>
         fs []>>
         cheat
    )>>
    `
                (seq i).count > (seq 0).count 

    ` by ( 
        `seq 0 = s` by METIS_TAC [rel_sequence_def]>> rfs[] >> 
        DECIDE_TAC
    )>>
    (* there exists a state in the sequance that  *)
    (*   will transition to a state equal to the  *)
    (*   final state                              *)
    `
             ?i'. ((seq i' ).count < (s.count +t))
                    /\ ((seq (SUC i'))=(seq i)) 
                    /\ ((seq' (SUC i'))=(seq' i))

    ` by METIS_TAC[EXISTS_PRE_STATE_lem]>>
    METIS_TAC[VC_def, EXISTS_PRE_STATE_lem]
    
);
    

val  VC_RUN_EXISTS_lem = prove(
``! P t seq i s .
	VC uart_r P t /\
	NEX P t /\
	  SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
	  rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	  (seq i).count < s.count + t ==> 
            ! z_i.(
              m0_non_r_eq uart_r z_i (seq i)==>
                ? z_0.
                  !seq_z. (rel_sequence (NEXT_REL $= NextStateM0) seq_z z_0) ==>
                        ((seq_z i) = z_i) /\
                          m0_non_r_eq uart_r s z_0 /\
                          m0_r_eq uart_r z_0 z_i
            )
``,
    
    REPEAT STRIP_TAC>>
    EXISTS_TAC ``s with <|MEM := (\x. if (x IN uart_r) 
                                         then (z_i.MEM x)
                                         else (s.MEM x)) |>``>>
    REPEAT STRIP_TAC>>
    `m0_non_r_eq uart_r s (s with MEM := (λx. if x ∈ uart_r then z_i.MEM x else s.MEM x)) /\
     m0_r_eq uart_r (s with MEM := (λx. if x ∈ uart_r then z_i.MEM x else s.MEM x)) z_i` by (
           SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [
                m0Theory.m0_state_accfupds,m0_non_r_eq_def, m0_r_eq_def, mem_eq_def
           ]
    )>>
    Q.ABBREV_TAC `z_0=(s with MEM := (λx. if x ∈ uart_r then z_i.MEM x else s.MEM x))`>>
    (MP_TAC o
        Q.SPECL [`P`, `(seq (i:num)).count-s.count`, `seq`, `seq_z`, `i`, `s`, `z_0`, `uart_r`])
        FINAL_STATE_EQ_lem >>
    (* apply weakening *)
    
    `s.count <= (seq i).count` by METIS_TAC[SEQ_MONO_B, DECIDE ``0n<=i:num``,rel_sequence_def ]>>
    `((seq i).count = s.count + ((seq i).count − s.count)) ` by DECIDE_TAC>>
    `((seq i).count -s.count) <= t` by DECIDE_TAC>>
    `VC uart_r P ((seq i).count -s.count)∧ NEX P ((seq i).count -s.count)` by METIS_TAC[VC_WEAKEN_lem, NEX_WEAKEN_lem]>>
        ASM_SIMP_TAC std_ss[]>>
	METIS_TAC[m0_r_eq_trans_thm, m0_r_eq_antisym_thm,
                  m0_non_r_eq_trans_thm, m0_non_r_eq_antisym_thm,
                  eq_lem,rel_sequence_def]
);

val   VC_NIT_STEP_thm = store_thm("VC_NIT_STEP_thm",
``  ! P t s seq i.
	VC uart_r P t /\
	NEX P t /\
	SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
	rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	(seq i).count < s.count + t ==> NIT_STEP uart_r (seq i)``,

    REPEAT STRIP_TAC >>
    SIMP_TAC std_ss [NIT_STEP_thm]>>
    GEN_TAC>>
    rename1 `m0_non_r_eq uart_r (seq i) z_i`>>
    STRIP_TAC>>
     `              
            ∃z_0.
                ∀seq_z.
                    rel_sequence (NEXT_REL $= NextStateM0) seq_z z_0 ⇒
                    (seq_z i = z_i)/\ m0_non_r_eq uart_r s z_0 /\ m0_r_eq uart_r z_0 z_i

     `by METIS_TAC[ VC_RUN_EXISTS_lem, m0_non_r_eq_antisym_thm]>>


     `
              ?seq_z . rel_sequence (NEXT_REL $= NextStateM0) seq_z z_0

     ` by( METIS_TAC[SEQUENCE_EXISTS_THM])>>

     `              
                     (seq_z i = z_i)/\ m0_non_r_eq uart_r s z_0/\m0_r_eq uart_r z_0 z_i
     ` by METIS_TAC[]>>
     rm_assum `∀seq_z._`>>
     `              
          m0_non_r_eq uart_r (seq (SUC i)) (seq_z (SUC i)) ∧
          m0_r_eq uart_r (seq_z 0) (seq_z (SUC i))
     `   by METIS_TAC[VC_def] >>
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
    rm_assum `VC _ _ _`>>
    rm_assum `NEX  _ _`>>
    METIS_TAC[m0_r_eq_trans_thm,m0_r_eq_antisym_thm, rel_sequence_def]
    
);
 


(* cosim *)
val COSIM'_def = Define `COSIM' P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (m0u_Next (seq' i)) (Next (seq i)) /\
        m0u_r_eq uart_r (seq' i)  (m0u_Next (seq' i))`;

val COSIM_def = Define `COSIM P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (seq' (SUC i)) (seq (SUC i)) /\
        m0u_r_eq uart_r (seq' i)  (seq' (SUC i))`;

val cosim_def = Define `cosim P c t = COSIM ((CODE_POOL m0_instr c) * P  ) t`;


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
        (((FST o FST) a).count =  b.count)/\
        (((FST o FST) a).exception =  b.exception)``,
    Cases_on `a`>> Cases_on `q`>> Cases_on `r`>>
    SIMP_TAC std_ss [m0u_m0_non_r_eq_def, m0_non_r_eq_def]
);

val VC_COSIM'_thm = Q.prove (
    `!P t.  ((VC uart_r P t) /\ (NEX P t)) ==> (COSIM' P t)`,
    SIMP_TAC std_ss [ COSIM'_def, PULL_FORALL]>>
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    STRIP_TAC>>
    Induct_on `i` >-
    (
        STRIP_TAC>>
        `((seq 0).count < (Next (seq 0)).count) ∧( (Next (seq 0) = seq (SUC 0)))` by
            METIS_TAC[NEX_thm]>>
        `NIT_STEP uart_r (seq 0)` by METIS_TAC[VC_NIT_STEP_thm]>>
        METIS_TAC[rel_sequence_def, AXI, m0u_r_eq_antisym_thm]
    )>>
    STRIP_TAC >>
    `(seq i).count < s.count + t` by (
        METIS_TAC[SEQ_MONO_LEM]
    )>>
    FULL_SIMP_TAC std_ss []>>
    ` (seq i).count < (Next (seq i)).count ∧
    (Next (seq i) = seq (SUC i))` by METIS_TAC[NEX_thm]>>
    ` (seq (SUC i)).count < (Next (seq (SUC i))).count ∧
    (Next (seq (SUC i)) = seq (SUC(SUC i)))` by METIS_TAC[NEX_thm]>>
    `NIT_STEP uart_r (seq (SUC i) )` by METIS_TAC[VC_NIT_STEP_thm]>>
    `m0u_Next (seq' i) =  (seq' (SUC i))` by (
        ` ((FST ∘ FST) (m0u_Next (seq' i))).exception = NoException` by METIS_TAC[LEM1,NEX_def]>>
        `if ∃x. NEXT_REL $= NextStateM0U (seq' i) x then
               NEXT_REL $= NextStateM0U (seq' i) (seq' (SUC i))
             else seq' (SUC i) = seq' i` by METIS_TAC [rel_sequence_def]>>
        rfs[rel_sequence_def, NextStateM0U_def,
                               NEXT_REL_def, LET_DEF, PULL_EXISTS]
    )>>
    METIS_TAC [m0u_r_eq_antisym_thm, AXI]
);


(* Theorem 2 in repport *)
val VC_COSIM_thm = Q.prove(`!P t.  ((VC uart_r P t) /\ (NEX P t)) ==> (COSIM P t)`,
    fs[COSIM_def, PULL_FORALL]>>
    REPEAT gen_tac>> strip_tac >>strip_tac>>
    `COSIM' P t` by fs[VC_COSIM'_thm]>>
    ` m0u_m0_non_r_eq uart_r (m0u_Next (seq' i)) (Next (seq i)) ∧
             m0u_r_eq uart_r (seq' i) (m0u_Next (seq' i))` by ( 
        fs[COSIM'_def]>> METIS_TAC[]
    )>>
    (`Next (seq i) = seq (SUC i)` by(
        (mp_tac (Q.SPECL [`P`, `t`, `s`, `seq`, `i`] NEX_thm))>>
        fs[]))>>
    `m0u_Next (seq' i) = seq' (SUC i)` by (
        (`((Next (seq i)).exception = NoException)` by (
            fs[NEX_def] >>
            METIS_TAC[])
        )>>
        (`(((FST ∘ FST)(m0u_Next (seq' i))).exception = NoException)` by METIS_TAC[LEM1])>>
        rfs[NextStateM0U_def, rel_sequence_def, NEXT_REL_def]>>
        `m0u_Next (seq' i) = seq' (SUC i)` by METIS_TAC[]
    )>>
    fs[]
);

val FINAL_STATE_EQ_thm = Q.store_thm ("VC_COSIM_thm",
    `!P t.  ((VC uart_r P t) /\ (NEX P t)) ==> ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count = s.count + t) )==>
        m0u_m0_non_r_eq uart_r (seq' ( i)) (seq ( i)) /\
        m0u_r_eq uart_r (seq' 0)  (seq' ( i))`,
    cheat);
     
(* 
`!P t.  ((VC uart_r P t) /\ (NEX P t)) ==> (COSIM2 P t)`,
        REPEAT STRIP_TAC >>
       `COSIM P t ` by fs[ VC_COSIM_thm]>> 
       fs[COSIM2_def] >> 
        REPEAT GEN_TAC >>
             
       STRIP_TAC
       Q.PAT_X_ASSUM `COSIM P t` ( MP_TAC o Q.SPECL [`s`, `s'`, `seq`, `seq'`, `i`] o REWRITE_RULE [COSIM_def] )



       (MP_TAC o Q.SPECL [`P`, `t`])  NEX_thm
       fs[NEX_thm]
       STRIP_TAC
       METIS_TAC[]
*)
val _ = export_theory();
