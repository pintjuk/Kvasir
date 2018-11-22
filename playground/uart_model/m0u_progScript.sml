 (* set_trace "simplifier" 0; *)

open HolKernel Parse boolLib bossLib;
open uartTheory;
open pairTheory;
open progTheory;
open set_sepTheory;
open m0_NITTheory;
open m0_progTheory;
open uartTheory
open clockTheory;
open stateTheory m0_stepTheory;
open boolSimps;
open pred_setTheory;
open sep_helper;

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


val m0u_instr_def = Define`
    (m0u_instr (a,INL opc16) =
        {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((7 >< 0) opc16)));
        (m0_c (m0_c_MEM (a + 1w)), m0_d(m0_d_word8 ((15 >< 8) opc16)))}) /\
    (m0u_instr (a,INR opc32) =
        {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((23 >< 16) opc32)));
        (m0_c (m0_c_MEM (a + 1w)),m0_d (m0_d_word8 ((31 >< 24) opc32)));
        (m0_c (m0_c_MEM (a + 2w)),m0_d (m0_d_word8 ((7 >< 0) opc32)));
        (m0_c (m0_c_MEM (a + 3w)),m0_d (m0_d_word8 ((15 >< 8) opc32)))})`


(* Translate M0 separation logit to M0U separation logic *)

(* low level mapping *)
val TO_M0U_def = Define`
 TO_M0U = IMAGE (m0_c ## m0_d )
`;

(* Apply the property on the  *)
val TO_M0U_PROP_def = Define`
 TO_M0U_PROP= IMAGE TO_M0U
`;

(* transaltion theorems *)
(* TO_M0U prep sepration logic "linearity" *)

val star_2_m0u_thm = store_thm("star_2_m0u_thm",
    ``! a b. TO_M0U_PROP (a * b) = (TO_M0U_PROP a) * (TO_M0U_PROP b)``,
    SIMP_TAC std_ss [STAR_def, SPLIT_def, TO_M0U_PROP_def, TO_M0U_def]>>
    (* TODO: finish proof *)
    cheat
);

val cond_2_m0u_thm = store_thm("cond_2_m0u_thm",
    ``!x. TO_M0U_PROP (cond x) = (cond x)``,
    SIMP_TAC std_ss [cond_def,TO_M0U_PROP_def, TO_M0U_def]>>
    (* TODO: finish proof *)
    cheat
);

(* m0u abrivations *)
val instr_2_m0u_thm = store_thm( "instr_2_m0u_thm",
    ``TO_M0U o m0_instr = m0u_instr``,
    SIMP_TAC std_ss [FUN_EQ_THM]>>
    Cases_on `x`>> rename1 `(addr,inst)`>> Cases_on `inst`>>
    SIMP_TAC (std_ss ++ pred_setLib.PRED_SET_ss) [TO_M0U_def, m0u_instr_def, m0_instr_def]
);

val CODE_POOL_2_m0u_thm = store_thm( "CODE_POOL_2_m0u_thm",
``!code. TO_M0U_PROP (CODE_POOL m0_instr code) = CODE_POOL m0u_instr code``,
    FULL_SIMP_TAC (bool_ss) [TO_M0U_PROP_def, CODE_POOL_def]>>
    STRIP_TAC>>
cheat
    (* TODO: prove cheeted lemma  *)
    (* ` IMAGE (TO_M0U) (\s. s = BIGUNION (IMAGE m0_instr code)) = (λs. s = TO_M0U (BIGUNION (IMAGE m0_instr code)))` by  cheat>>
   ASM_SIMP_TAC std_ss [TO_M0U_def, IMAGE_BIGUNION, IMAGE_IMAGE]>>
   SIMP_TAC std_ss [GSYM TO_M0U_def, instr_2_m0u_thm]*)
);


(*
val count_2_m0u_thm = store_thm( "count_2_m0u_thm",
``!code. TO_M0U_PROP (m0_count) = CODE_POOL m0u_instr code``,

);*)

val PROP_2_m0u_RWR  = [star_2_m0u_thm, cond_2_m0u_thm, instr_2_m0u_thm, CODE_POOL_2_m0u_thm ];
(********************************************)
(*        Sep logic Domain theory           *)
(********************************************)

(* Convert memory region to seperation logic component set *)
val r2m0_c_set_def = Define`
    r2m0_c_set region = IMAGE m0_c_MEM region
`;


(* UART is separation logic version of uart region  *)
val UART_def = Define`
   UART = r2m0_c_set uart_r
`;

(* Domain of separation logic expression *)
val m0_DOM_def = Define`
    DOM (A:(m0_component # m0_data -> bool) -> bool) = (BIGUNION (IMAGE (IMAGE (FST)) A))
`;

val m0_DOM_STAR_thm = store_thm("m0_SDOM_STAR_thm", ``
!A  B x. DOM (A * B) x ⇒ (DOM A ∪ DOM B) x``,
    FULL_SIMP_TAC (std_ss ++ pred_setLib.PRED_SET_ss) [DISJOINT_DEF, UNION_DEF, FUN_EQ_THM, INTER_DEF, IN_DEF, STAR_def, SPLIT_def, m0_DOM_def, GSYM IMAGE_BIGUNION]>>
    METIS_TAC []
);


(* Intuitivly it seas like this should also be true,

   it colud be easer to use
 *)
val m0_DOM_STAR_2thm = prove(``!A B.  DOM (A * B) = (DOM A) UNION (DOM B)``, cheat);
val m0_DOM_COND_thm = prove(``!x. DOM(cond x) = {} ``, cheat);

(*
``DISJOINT (DOM ((m0_count 3) * {{(m0_c_MEM 0w, m0_d_word8 0w)}})) ((r2m0_c_set uart_r))``

(* TODO: ask Roberto why i cant use m0s_union to rewrite this shit *)

Ho_Rewrite.REWRITE_TAC[m0_DOM_STAR_2thm]
SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [
m0_count_def, r2m0_c_set_def, m0_component_distinct, DISJOINT_DEF, m0_DOM_def,uart_r_def]

STRIP_TAC

DB.find "m0_REG"

``{{(m0_c_count,m0_d_num (3 :num))}}=v`` *)

(********************************************)
(*          Uart model prog                 *)
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

val NextStateM0U_def = Define ` NextStateM0U s0 =
      (let
        s1  = m0u_Next s0
      in
         if ((FST o FST)s1).exception = NoException
         then SOME s1 else NONE)`;


val M0U_MODEL = Define `M0U_MODEL = (
    (* projection from record state to set of components: *)
    STATE m0u_proj,

    (* Next state relation*)
    NEXT_REL $= NextStateM0U,

    (* code to set of memory components *)
    m0u_instr,

    (* equality of states *)
    $=  :((m0_state # uart_state) # word32 list # word32 list)->
         ((m0_state # uart_state) # word32 list # word32 list)-> bool,

    (* Not sure what this is for, it does not seem to be uneful in the m0 model *)
    K F :((m0_state # uart_state) # word32 list # word32 list)-> bool
    )`;


(* ALTERNET def, might be a theorem 
val COSIM_def = Define `COSIM P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (seq' i) (seq i) /\
        m0u_r_eq uart_r s' (seq' i)/\
        m0u_m0_non_r_eq uart_r (seq' (SUC i)) (seq (SUC i)) /\
        m0u_r_eq uart_r s' (seq' (SUC i))`;

*)

val COSIM_def = Define `COSIM P t = ! s s' seq seq' i.
    ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
    rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
    rel_sequence (NEXT_REL $= NextStateM0U) seq' s' /\
    m0u_m0_non_r_eq uart_r s' s /\ ((seq i).count < s.count + t) )==>
        m0u_m0_non_r_eq uart_r (m0u_Next (seq' i)) (Next (seq i)) /\
        m0u_r_eq uart_r (seq' i)  (m0u_Next (seq' i))`;

val cosim_def = Define `cosim P c t = COSIM ((CODE_POOL m0_instr c) * P  ) t`;

val NEX_thm = Q.store_thm("NEX_thm",
    `! P t. 
        (NEX P t) ==> (! s seq i. 
            SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s /\
            rel_sequence (NEXT_REL $= NextStateM0) seq s /\
            (seq (i)).count < s.count + t ==>
                ((seq i).count < (Next(seq i)).count) /\ ((Next (seq i)) = (seq(SUC i))))`,
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


val NIT_COSIM_thm = Q.store_thm ("NIT_COSIM_thm",
    `!P t.  ((NIT uart_r P t) /\ (NEX P t)) ==> (COSIM P t)`,
    SIMP_TAC std_ss [ COSIM_def, PULL_FORALL]>>
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    STRIP_TAC>>
    Induct_on `i` >-(
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
        FULL_SIMP_TAC bool_ss [rel_sequence_def, NextStateM0U_def,
                               NEXT_REL_def, LET_DEF, PULL_EXISTS]>>
        METIS_TAC[optionTheory.option_CLAUSES, rel_sequence_def]
    )>>
    METIS_TAC [m0u_r_eq_antisym_thm, AXI]
);
(********************************************)
(*          Transfere properties            *)
(*                                          *)
(********************************************)

(*

first lemma for proving the TP theorem:
``!P s_m0 s_m0u.  DISJOINT (DOM P) UART  /\ P (m0_proj s_m0) /\ ((TO_M0U_PROP P) (m0u_proj s_m0u)) ==>
(m0u_m0_non_r_eq uart_r s_m0u s_m0)``


seccond lemma for proving the TP theorem

{P} c {Q} /\ DISJOINT (P UNION Q) UART ==> m
*)
             (*
val TP_thm = Q.store_thm("TP_thm",
    `!P C Q c t C.
        (SPEC M0_MODEL (P*m0_count c) C (Q*m0_count (c+t))) /\
        (cosim (P * m0_count c) C t) ==>
            (SPEC M0U_MODEL (TO_M0U_PROP (P * m0_count c)) C (TO_M0U_PROP(Q * m0_count (c+t))))`,

           REWRITE_TAC[SPEC_def, M0U_MODEL, RUN_def]>>
    REPEAT STRIP_TAC>>


FULL_SIMP_TAC std_ss [GSYM CODE_POOL_2_m0u_thm, GSYM star_2_m0u_thm]>>
FULL_SIMP_TAC std_ss [cosim_def, COSIM_def]>>

           Q.ABBREV_TAC `Pri = (CODE_POOL m0_instr C * (Q * m0_count (c + t))) * r`>>
           Q.ABBREV_TAC `Post = CODE_POOL (λc. TO_M0U (m0_instr c)) C *
                  TO_M0U_PROP (Q * m0_count (c + t))`

        (DISJOINT (DOM P) UART) /\
        (DISJOINT (DOM Q) UART) ==>
    REPEAT STRIP_TAC
    cheat);*)
(*
val WS_COSIM_thm = Q.store_thm("WS_COSIM_thm",
    `!P P' t t'. COSIM P t /\ t' < t  /\ (SEP_IMP P' P) ==> COSIM P' t'`,
    SIMP_TAC arith_ss [COSIM_def, PULL_FORALL]>>
    REPEAT STRIP_TAC>>(
        Q.PAT_X_ASSUM `!s s' seq seq' i._` (MP_TAC o Q.SPECL [`s`, `s'`, `seq`, `seq'`, `i`] )>>
        REPEAT STRIP_TAC>>
        ` (seq i).count ≤ t+s.count` by DECIDE_TAC>>
        `SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s` by (
        REV_FULL_SIMP_TAC std_ss [SEP_IMP_def, STAR_def,SEP_REFINE_def]>>
        METIS_TAC [])>>
        METIS_TAC []
    )
);
*)

val _ = export_theory();
