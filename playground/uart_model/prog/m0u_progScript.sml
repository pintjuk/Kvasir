 (* set_trace "simplifier" 0; *)

open HolKernel Parse boolLib bossLib;
open uartTheory;
open pairTheory;
open progTheory;
open set_sepTheory;
open m0_progTheory;
open uartTheory
open stateTheory m0_stepTheory;
open boolSimps;
open pred_setTheory;

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
    (* TODO: prove cheeted lemma  *)
    ` IMAGE (TO_M0U) (\s. s = BIGUNION (IMAGE m0_instr code))
= (λs. s = TO_M0U (BIGUNION (IMAGE m0_instr code)))` by  cheat>>
   ASM_SIMP_TAC std_ss [TO_M0U_def, IMAGE_BIGUNION, IMAGE_IMAGE]>>
   SIMP_TAC std_ss [GSYM TO_M0U_def, instr_2_m0u_thm]
);


(*
val count_2_m0u_thm = store_thm( "count_2_m0u_thm",
``!code. TO_M0U_PROP (m0_count) = CODE_POOL m0u_instr code``,
                                            
);*)

val PROP_2_m0u_RWR  = [star_2_m0u_thm, cond_2_m0u_thm, instr_2_m0u_thm, CODE_POOL_2_m0u_thm ]
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
    DOM A = (BIGUNION (IMAGE (IMAGE (FST)) A))
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

val NextStateM0U_def = Define ` NextStateM0U s0 =
      (let
        s1  = m0u_Next s0
      in
          if  (((FST o FST)s1).exception = NoException)
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

val _ = export_theory();
