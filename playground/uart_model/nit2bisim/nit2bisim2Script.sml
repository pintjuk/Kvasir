(*
         loadPath := ("../uart"::(!loadPath));
         loadPath := ("../prog"::(!loadPath));
         loadPath := ("../clock"::(!loadPath));
 *)
open HolKernel Parse boolLib bossLib;
open m0_NITTheory
open uartTheory
open m0u_progTheory
open m0_progTheory
open stateTheory m0_stepTheory;
open boolSimps;
open pred_setTheory;
open m0_progTheory;
open pairTheory;
open progTheory;
open set_sepTheory;
open clockTheory;

val _ = new_theory "nit2bisim2";

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
               ((seq (i)).count < s.count+ t))==>   
	           ((seq i).count < (Next(seq i)).count) /\
                   ((Next (seq (i))).exception = NoException) `;

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
               ((seq i).count < s.count+t)) ==>   
                   m0_non_r_eq region (seq (SUC i)) (seq' (SUC i)) /\
                   m0_r_eq region (seq' 0) (seq' (SUC i))
`;




val NIT_NIT_STEP_thm = store_thm("NIT_NIT_STEP_thm",
``  ! P t region. 
        ((NEX P t)/\ (NIT region P t)) = ! s seq i . (
        SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
        rel_sequence (NEXT_REL $= NextStateM0) seq s /\
        (seq i).count < s.count + t ==> NIT_STEP region (seq i))``,
        cheat
);

(* bisim *)
val SEQ_MONO_LEM = Q.prove( `!seq s i t.
    (rel_sequence (NEXT_REL $= NextStateM0) seq s)/\
    ((seq (SUC i)).count < s.count + t)==> ((seq i).count < s.count + t)`,
    REPEAT GEN_TAC>>
    (MP_TAC o Q.SPECL[`s`,`i`,`SUC i`,`seq`] ) SEQ_MONO_B>>
    ASM_SIMP_TAC std_ss []>>
    METIS_TAC [ DECIDE ``( x:num <= y:num /\ y < z:num ) ==> (x < z) ``]
);

val COSIM'_def = Define `COSIM' P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (m0u_Next (seq' i)) (Next (seq i)) /\
        m0u_r_eq uart_r (seq' i)  (m0u_Next (seq' i))`;

val COSIM''_def = Define `COSIM'' P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (seq' (SUC i)) (seq (SUC i)) /\
        m0u_r_eq uart_r (seq' i)  (seq' (SUC i))`;

val COSIM_def = Define `COSIM P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count <= s.count + t) )==>
        m0u_m0_non_r_eq uart_r (seq' ( i)) (seq ( i)) /\
        m0u_r_eq uart_r (seq' 0)  (seq' ( i))`;


val cosim_def = Define `cosim P c t = COSIM ((CODE_POOL m0_instr c) * P  ) t`;

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


val NIT_COSIM'_thm = Q.store_thm ("NIT_COSIM'_thm",
    `!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM' P t)`,
    SIMP_TAC std_ss [ COSIM'_def, PULL_FORALL]>>
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    STRIP_TAC>>
    Induct_on `i` >-
    (
        STRIP_TAC>>
        `((seq 0).count < (Next (seq 0)).count) ∧( (Next (seq 0) = seq (SUC 0)))` by
            METIS_TAC[NEX_thm]>>
        `NIT_STEP uart_r (seq 0)` by METIS_TAC[NIT_NIT_STEP_thm]>>
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
    `NIT_STEP uart_r (seq (SUC i) )` by METIS_TAC[NIT_NIT_STEP_thm]>>
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


val NIT_COSIM''_thm = Q.prove(`!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM'' P t)`,
    fs[COSIM''_def, PULL_FORALL]>>
    REPEAT gen_tac>> strip_tac >>strip_tac>>
    `COSIM' P t` by fs[NIT_COSIM'_thm]>>
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

val NIT_COSIM_thm = Q.store_thm ("NIT_COSIM_thm",
    `!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM P t)`,
                           (* use NIT_COSIM''_thm *)
    cheat);
     
(* 
`!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM2 P t)`,
        REPEAT STRIP_TAC >>
       `COSIM P t ` by fs[ NIT_COSIM_thm]>> 
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
