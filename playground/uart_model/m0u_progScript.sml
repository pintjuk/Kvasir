open HolKernel Parse boolLib bossLib;
open uartTheory
open progTheory 
open set_sepTheory
open m0_NITTheory
open uartTheory
open clockTheory
open stateTheory m0_stepTheory
open boolSimps
open pred_setTheory

val _ = new_theory "m0u_prog";
(********************************************)
(*           UART separation logic          *)
(*                                          *)
(********************************************)

val _= Datatype `m0u_component = m0_c m0_component
                               | m0u_c_Input 
                               | m0u_c_Output
                               | m0u_c_RXD
                               | m0u_c_TXD
                               | m0u_c_RXDRDY
                               | m0u_c_TXDRDY`;

val _= Datatype `m0u_data = m0_d m0_data
                          | m0u_d_stream (word32 list)
                          | m0u_d_word32 word32
                          | m0u_d_bool bool`;


val m0u_proj_def = Define `
m0u_proj ((s,u),input,output) =
     (λa.
         case a of
	   m0_c b => m0_d (m0_proj s b)
         | m0u_c_Input => m0u_d_stream input
	 | m0u_c_Output => m0u_d_stream output
         | m0u_c_RDX => m0u_d_word32 u.RXD
         | m0u_c_TXD => m0u_d_word32 u.TXD
         | m0u_c_RDXRDY => m0u_d_bool u.TXDRDY
         | m0u_c_TXDRDY => m0u_d_bool u.RXDRDY) 
`; 
       
(* Translate M0 separation logit to M0U separation logic *)  

val TO_M0U_def = Define`
 TO_M0U = IMAGE (m0_c ## m0_d )
`;

val TO_M0U_def = Define`
 TO_M0U_PROP= IMAGE TO_M0U
`;

(********************************************)
(*        Sep logic Domain theory           *)
(********************************************)
val r2m0_c_set_def = Define`
r2m0_c_set region = IMAGE m0_c_MEM region
`;

val m0_SDOM_def = Define`
SDOM A = (BIGUNION (IMAGE (IMAGE (\(c,_).c)) A)) `;

val m0_SEP_INV_UNDER_NON_R_EQ_thm = prove(
``!P region s s'. DISJOINT (SDOM P) (r2m0_c_set region) 
    /\ SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s 
    /\ m0_non_r_eq region s s' ==>
	SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s'``,
cheat);

(********************************************)
(*          Uart model prog                 *)
(*                                          *)
(********************************************)
val NextStateM0U_def = Define ` NextStateM0U ((s0,u0),I0,O0) =
      (let
        ((s1,u1),I1,O1)  = m0u_Next ((s0,u0),I0,O0)
      in
          if (~u1.unpredictable /\ (s1.exception = NoException))
         then SOME ((s1,u1),I1,O1) else NONE)`;

val M0U_MODEL = Define `M0U_MODEL = (
    STATE m0u_proj,
    NEXT_REL $= NextStateM0U,(\c. TO_M0U (m0_instr c)),
    $=  :((m0_state # uart_state) # word32 list # word32 list)-> 
         ((m0_state # uart_state) # word32 list # word32 list)-> bool,
    K F :((m0_state # uart_state) # word32 list # word32 list)-> bool
    )`;

val COSIM_def = Define ` COSIM P t = ! s s' seq seq' i.   
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count <= s.count + t) )==>   
	m0u_m0_non_r_eq uart_r (seq' i) (seq i) /\
	m0u_r_eq uart_r s' (seq' i)`;


val m0_non_r_eq_exists_thm = prove(``!s region.?s'. m0_non_r_eq region s s'``,
     METIS_TAC [m0_non_r_eq_refl_thm]
);

   (** third attempt with stronger induction assumption **) 
val NIT_COSIM_thm = Q.store_thm ("NIT_COSIM_thm", 
    `!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM P t)`, 
    SIMP_TAC std_ss [ COSIM_def, PULL_FORALL]>>
    (* Strengthen induction hypothesis  *)
    `!P t s s' s_hat seq seq'  seq_hat i .
        (m0_non_r_eq uart_r s s') /\
	NIT uart_r P t /\
	NEX P t ==>
	SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
	rel_sequence (NEXT_REL $= NextStateM0) seq s /\
	rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
	rel_sequence (NEXT_REL $= NextStateM0U) seq_hat s_hat /\
	m0u_m0_non_r_eq uart_r s_hat s /\ (seq i).count <= s.count + t ==>
        m0_non_r_eq uart_r (seq i) (seq' i) /\
        m0_r_eq uart_r s' (seq' i) /\
	m0u_m0_non_r_eq uart_r (seq_hat i) (seq i) /\
	m0u_r_eq uart_r s_hat (seq_hat i) ` suffices_by(
            METIS_TAC [m0_non_r_eq_exists_thm, SEQUENCE_EXISTS_THM]
    )>>
    REPEAT GEN_TAC>>
    Induct_on `i`>-(   
        `s.count <= s.count +t` by DECIDE_TAC>>
	METIS_TAC [m0u_m0_non_r_eq_def, m0u_r_eq_refl_thm,
                   m0_r_eq_refl_thm , rel_sequence_def]
    )>>
    STRIP_TAC>>STRIP_TAC>>
    `(seq i).count <= s.count + t ` by (
	(MP_TAC o Q.SPECL [`s`,`i`, `SUC i`, `seq`]) SEQ_MONO_B >>
	ASM_SIMP_TAC std_ss []>>
	DECIDE_TAC)>>
    FULL_SIMP_TAC std_ss []>>
    
    Q.PAT_ASSUM `NIT uart_r _ _` (MP_TAC o Q.SPECL [`s`, `s'`, `seq`, `seq'`, `SUC i`]
                                           o SIMP_RULE std_ss [ NIT_def])>>
    FULL_SIMP_TAC std_ss []>>
    STRIP_TAC >>

    (* should get from from NEX: *)

     `(seq(SUC i) = Next (seq(i))) /\ ((Next (seq i)).exception = NoException)` by (
	Q.PAT_X_ASSUM `NIX P t` (
            MP_TAC o Q.SPECL [`s`, `seq`, `SUC i`] o
	    REWRITE_RULE [NEX_def])>>
	FULL_SIMP_TAC (std_ss++LET_ss) [
	    rel_sequence_def, NEXT_REL_EQ,
            NextStateM0_def]>>
        METIS_TAC []  
      )>>
   
      

    `(seq'(SUC i) = Next (seq'(i))) ` by(
     `((seq' (SUC i)).exception = NoException)` by  FULL_SIMP_TAC std_ss[m0_non_r_eq_def]>>
	FULL_SIMP_TAC (std_ss++LET_ss) [
	    rel_sequence_def, NEXT_REL_EQ,
            NextStateM0_def]>>
	Cases_on  `(Next (seq' i)).exception = NoException`>- (
	    METIS_TAC [])>>
	Q.PAT_ASSUM `!n.
		if (Next (seq' n)).exception = NoException then
		    Next (seq' n) = seq' (SUC n)
		else seq' (SUC n) = seq' n` (MP_TAC o Q.SPECL [`i`])>>
	`(seq i).count = (Next(seq i)).count` suffices_by (
	    (MP_TAC o Q.SPEC `seq (i:num)`) NEXT_MONO>>
	    ASM_SIMP_TAC arith_ss [])>>
	FULL_SIMP_TAC std_ss [m0_non_r_eq_def] >>
	METIS_TAC[]
    )>>
    FULL_SIMP_TAC std_ss []>>

    (* from NIT_STEP_thm and 16, 12, 13 *)
    `NIT_STEP uart_r (seq i)`  suffices_by cheat
    
    ASM_SIMP_TAC std_ss  [NIT_STEP_thm, m0_non_r_eq_antisym_thm, m0_non_r_eq_trans_thm, m0_r_eq_trans_thm, m0_r_eq_antisym_thm]
    
    DB.find "NIT_STEP_thm"
    SIMP_RULE std_ss [PULL_FORALL] NIT_STEP_thm
    
    (MP_TAC o Q.SPECL [`seq (i:num)`, `seq_hat (i:num)`]) AXI>>
    ASM_SIMP_TAC std_ss [NIT_STEP_def, NIT_STEP_from_def]>> 
DB.find "NIT_STEP_from"
    
    (* uart does not change, so uart is still predictable *)
    `seq_hat(SUC i) = m0u_Next (seq_hat i)` by cheat>>
    METIS_TAC [m0u_r_eq_trans_thm,  m0u_r_eq_antisym_thm]
);

    

(********************************************)
(*          Transfere properties            *)
(*                                          *)
(********************************************)



val TP_def = Q.store_thm(
    "TP_def",
    `!P C Q c t. (SPEC M0_MODEL (P*m0_count c) C (Q*m0_count (c+t))) /\ 
	(COSIM P t) /\  

(!SET. P SET==>  DISJOINT SET UART) /\
(!SET. Q SET==>  DISJOINT SET UART) ==>

 
	    (SPEC M0U_MODEL (TO_M0U_PROP (P*m0_count c)) C (TO_M0U_PROP(Q*m0_count (c+t))))`,
    cheat);

val WS_COSIM_thm = Q.store_thm("WS_COSIM_thm",
    `!P P' t t'. COSIM P t /\ t' < t  /\ (SEP_IMP P' P) ==> COSIM P' t'`,
    SIMP_TAC arith_ss [COSIM_def, PULL_FORALL]>>
    REPEAT STRIP_TAC>>(
	Q.PAT_X_ASSUM `!s s' seq seq' i F._` (MP_TAC o Q.SPECL [`s`, `s'`, `seq`, `seq'`, `i`, `F'`] )>>
	REPEAT STRIP_TAC>>
	` (seq i).count ≤ t` by DECIDE_TAC>>
	`SEP_REFINE (P * F') $= (STATE m0_proj) s` by (
	REV_FULL_SIMP_TAC std_ss [SEP_IMP_def, STAR_def,SEP_REFINE_def]>>
	METIS_TAC [])>>
	METIS_TAC []
    )
);


val _ = export_theory();
