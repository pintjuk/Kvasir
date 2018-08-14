loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/model"::(!loadPath));
loadPath := ("/Home/daniil/HOL/examples/l3-machine-code/common"::(!loadPath));
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/prog"::(!loadPath));
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));

open stateTheory m0_stepTheory boolSimps
open wordsTheory;
open m0Theory;
open boolSimps;
open optionTheory;
open m0_progLib;
open m0_progTheory;
open progTheory;

val _ = new_theory "m0_flowTheory";

val mem_eq_def = Define`
mem_eq region mem1 mem2 = 
   (!x. x IN region ==> ((mem1 x) = (mem2 x)))
`;

val m0_r_eq_def = Define `
m0_r_eq region s1 s2 = 
   (mem_eq region s1.MEM s2.MEM)
`;


val m0_non_r_eq_def = Define `
    m0_non_r_eq region s1 s2 = (
	(s1.AIRCR = s2.AIRCR)/\
	(s1.CCR = s2.CCR)/\
	(s1.CONTROL = s2.CONTROL)/\
	(s1.CurrentMode = s2.CurrentMode)/\
	(s1.ExceptionActive = s2.ExceptionActive)/\
	(s1.NVIC_IPR = s2.NVIC_IPR)/\
	(s1.PRIMASK = s2.PRIMASK)/\
	(s1.PSR = s2.PSR)/\
	(s1.REG = s2.REG)/\
	(s1.SHPR2 = s2.SHPR2)/\
	(s1.SHPR3 = s2.SHPR3)/\
	(s1.VTOR = s2.VTOR)/\
	(s1.count = s2.count)/\
	(s1.exception = s2.exception)/\
	(s1.pcinc = s2.pcinc)/\
	(s1.pending = s2.pending)/\
	(mem_eq {x|  x NOTIN region } s1.MEM s2.MEM))`;

(** There is no flow to a memory region from the rest of the state 
    During the next tranisition

    for arbitrary content of the region, the next instruciton does not change the content of the region
**)
val no_step_flow_to_def = Define` 
 no_step_flow_to region s = (
  !s'.  m0_non_r_eq region s s' ==> m0_r_eq region s' (Next s') 
 )`;

(** There is no information flow to the rest of the state from this region 
    During the next tranisition 
    
    Swaping out the content of the region arbitraraly does not affect the execution of the rest of the state.
**)
val no_step_flow_from_def = Define` 
 no_step_flow_from region s = (
  !s'. m0_non_r_eq region s s'==> m0_non_r_eq region (Next s) (Next s') 
)`;

val no_step_flow_def = Define`
no_step_flow region s = (no_step_flow_from region s) /\ (no_step_flow_to region s) 
`;

val no_flow_run_at_def = Define`
no_flow_run_at region s i = let 
 (to_set,next,instr,less,allow) = M0_MODEL
in ! s' seq seq'.   m0_non_r_eq region s s' /\ 
               rel_sequence next seq  s /\
               rel_sequence next seq' s' ==>   
                   m0_non_r_eq region (seq i) (seq' i) /\
                   m0_r_eq region s' (seq' i)`;

val no_flow_run_upto_def = Define`
no_flow_run_upto region s i = let 
 (to_set,next,instr,less,allow) = M0_MODEL
in ! s' seq seq' i'.  0<i'/\ i' <= i /\
               m0_non_r_eq region s s' /\ 
               rel_sequence next seq  s /\
               rel_sequence next seq' s' ==>   
                   m0_non_r_eq region (seq i') (seq' i') /\
                   m0_r_eq region s' (seq' i')`;

SIMP_RULE (std_ss++LET_ss) [RunM0_SEQUENCE_THM, M0_MODEL_def] no_flow_run_upto_def

``! s region. ((Next s).exception = NoException) ==> (no_step_flow region s =  no_flow_run_upto region s 1)``


SIMP_TAC (std_ss++boolSimps.LET_ss) [
                 no_step_flow_from_def, no_step_flow_to_def,
                 no_flow_run_upto_def, no_step_flow_def, M0_MODEL_def, RunM0_SEQUENCE_THM, M0_MODEL_def] 

SIMP_TAC (std_ss) [PULL_FORALL]
SIMP_TAC (std_ss++CONJ_ss) [DECIDE ``!i.(0n< i /\ i <=1) ==> (i=1)``]
ONCE_REWRITE_TAC [ DECIDE ``1n =(SUC 0n)``]
ASM_SIMP_TAC (std_ss++LET_ss) [RunM0_def]
EQ_TAC
>-(

REPEAT STRIP_TAC>>

)
DB.match [] ``((!a._)<=> (!a._) )=(!a._<=>_)``



STRIP_TAC

	Q.PAT_X_ASSUM `!x:m0_state x1:m0_state._` (fn x =>
            MP_TAC (SPECL [``s':m0_state``, ``s':m0_state``] x))>>
	ASM_SIMP_TAC std_ss []
	


    REPEAT STRIP_TAC>>(
	`i'=1` by DECIDE_TAC>>
	FULL_SIMP_TAC (arith_ss ++ boolSimps.LET_ss) [NEXT_REL_EQ, NextStateM0_def, progTheory.rel_sequence_def
	]>>
	Q.PAT_X_ASSUM `!x:num._` (fn x => MP_TAC (SPEC ``0:num`` x))>>
	Q.PAT_X_ASSUM `!x:num._` (fn x => MP_TAC (SPEC ``0:num`` x))>>
	Q.PAT_X_ASSUM `!x:m0_state._` (fn x =>
            MP_TAC (SPEC ``(seq' (0:num)):m0_state`` x))>>
	Q.PAT_X_ASSUM `!x:m0_state._` (fn x =>
            MP_TAC (SPEC ``(seq' (0:num)):m0_state`` x))>>
	FULL_SIMP_TAC (std_ss) [m0_non_r_eq_def]>>
	METIS_TAC []
)


SIMP_TAC (std_ss++boolSimps.LET_ss) [
                 no_step_flow_from_def, no_step_flow_to_def,
                 no_flow_run_upto_def, no_step_flow_def, M0_MODEL_def]>>

REPEAT STRIP_TAC>>
EQ_TAC
>-(
    REPEAT STRIP_TAC>>(
	`i'=1` by DECIDE_TAC>>
	FULL_SIMP_TAC (arith_ss ++ boolSimps.LET_ss) [NEXT_REL_EQ, NextStateM0_def, progTheory.rel_sequence_def
	]>>
	Q.PAT_X_ASSUM `!x:num._` (fn x => MP_TAC (SPEC ``0:num`` x))>>
	Q.PAT_X_ASSUM `!x:num._` (fn x => MP_TAC (SPEC ``0:num`` x))>>
	Q.PAT_X_ASSUM `!x:m0_state._` (fn x =>
            MP_TAC (SPEC ``(seq' (0:num)):m0_state`` x))>>
	Q.PAT_X_ASSUM `!x:m0_state._` (fn x =>
            MP_TAC (SPEC ``(seq' (0:num)):m0_state`` x))>>
	FULL_SIMP_TAC (std_ss) [m0_non_r_eq_def]>>
	METIS_TAC [])
)>>

STRIP_TAC>>
STRIP_TAC>>


Q.ABBREV_TAC `(seq = RunM0 s )`>>
Q.ABBREV_TAC `(seq' = RunM0 s')`
 
FULL_SIMP_TAC arith_ss [RunM0_SEQUENCE_THM]
Q.PAT_X_ASSUM `!s' i'._` (fn x => MP_TAC (SPECL 
    [``s':m0_state``, 
     ``1n``
    ] x))>>



STRIP_TAC
REWRITE_TAC [ DECIDE ``1= SUC 0`` ]
ASM_SIMP_TAC (std_ss++LET_ss) [RunM0_def]

IF_CASES_TAC

REPEAT STRIP_TAC

FULL_SIMP_TAC std_ss []
`Next`


Q.PAT_X_ASSUM `!x:num._` (fn x => MP_TAC (SPEC 
    ``if 0:num then s:m0_state else 
    if 1 then (Next s) 
    else (Next s)`` x))>>

DB.find "NextStateM0"
DB.find "rel_sequence"

SIMP_CONV (bool_ss++boolSimps.LET_ss++boolSimps.UNWIND_ss) [PULL_EXISTS, rel_sequence_def, NEXT_REL_EQ, NextStateM0_def] ``rel_sequence (NEXT_REL $= NextStateM0) seq s`` 

(*****************************)

val M0_SEQUENCE_THM = prove(`` rel_sequence (NEXT_REL $= NextStateM0) seq s <=>
  (seq 0 = s) ∧ !n. if (Next(seq n)).exception = NoException then seq (n+1) = Next (seq n) else seq (n+1) = seq n``,
    SIMP_TAC (std_ss++boolSimps.LET_ss++boolSimps.COND_elim_ss) [
	DECIDE ``SUC n = n + 1n``, rel_sequence_def, NEXT_REL_EQ, NextStateM0_def]>>
    METIS_TAC[]);


val RunM0_def = Define `RunM0 s0 k = if k=0n then s0 
                                 else case (NextStateM0 s0) of 
                                   NONE   => s0 
                                 | SOME (s1)=> RunM0 s1 (k-1)`

val RunM0_def = Define `(RunM0 s 0n = s) /\
                         (RunM0 s k = let 
                           s' = RunM0 s (k-1)
                        in if (Next (s')).exception = NoException 
                           then Next(s')
                           else s')`


val RunM0_SEQUENCE_THM = prove(
``! s seq.
  (rel_sequence (NEXT_REL $= NextStateM0) seq s)  <=> (seq = (RunM0 s))``,
    REPEAT STRIP_TAC>>
    SIMP_TAC std_ss [M0_SEQUENCE_THM, FUN_EQ_THM, PULL_FORALL]>>
    EQ_TAC>-(
	SPEC_TAC (``s:m0_state``, ``s:m0_state``)>>
	SIMP_TAC std_ss [ PULL_FORALL]>>
	Induct_on `x`>-( 
	    METIS_TAC[RunM0_def ]
	) >>
	REPEAT STRIP_TAC >>
	ONCE_REWRITE_TAC [RunM0_def]>>
	SIMP_TAC (arith_ss++LET_ss) [NextStateM0_def, optionTheory.option_CLAUSES] >>
	Q.PAT_X_ASSUM `!s:m0_state._` (fn x=> MP_TAC (SPEC ``s:m0_state`` x))>>
	ASM_SIMP_TAC std_ss[]>>
	Q.PAT_X_ASSUM `!n._` (fn x=> MP_TAC (SPEC ``x:num`` x))>>
	METIS_TAC[DECIDE ``SUC x= x+1``]
    )>>
    SIMP_TAC std_ss [ PULL_FORALL]>>
    REPEAT STRIP_TAC >-  
    (SIMP_TAC std_ss [RunM0_def])>>
    IF_CASES_TAC>> ASM_SIMP_TAC (arith_ss++LET_ss) [RunM0_def, DECIDE ``n+1=SUC n``]
)

    
PAT_X_ASSUM ``!a._`` (fn x=> MP_TAC (SPECL [``0n``] x))

``let v (a:num) (b:num) = a+b in 
( 1n v 3n)``
ME
DB.match [] ``rel_sequence r seq s``
DB.find "NOW_def"
DB.find "TEMPORAL_def"
``! s seq.  (rel_sequence (NEXT_REL $= NextStateM0) seq s) /\ => (seq = (RunM0 s))``
IF_CASES_TAC>>


Induct_on `x`

FULL_SIMP_TAC (bool_ss) [m0_non_r_eq_def ]

ASM_SIMP_TAC std_ss[]


ASM_REWRITE_TAC []
REV_FULL_SIMP_TAC std_ss []
ASM_SIMP_TAC std_ss []

SIMP_TAC arith_ss [, (GEN_ALL o DECIDE) ``(0<i:num) /\ (i<=1) ==> (i=1)``]

EQ_TAC
STRIP_TAC
SIMP_TAC (std_ss++CONJ_ss) [(DECIDE) ``((0<i':num) /\ (i'<=1)) ==> (i'=1)``]

set_trace "simplifier" 0;
set_trace "simplifier" 2;
Ho_Rewrite.ONCE_REWRITE_TAC [MONO_AND]








(* uart specific *)

val uart_region_def = Define`
(* TODO: change to bit masking? *)
uart_region = {addr| addr >= 0x40002000w /\ addr <= 0x4000256Cw}
`;


val no_if_to_uart_def = Define`
no_if_to_uart s = no_flow_to uart_region s`;


val no_if_from_uart_def = Define`
no_if_from_uart s = no_flow_from uart_region s`;


val ward_region_def = Define`
(* TODO: change to bit masking? *)
ward_region x = {addr| (addr = x) \/ (addr = x+1w) \/
                         (addr = x+2w) \/ (addr = x+3w)}
`;

val no_if_to_word_def = Define`
no_if_to_word addr s = no_flow_to ward_region s`;


val no_if_from_word_def = Define`
no_if_from_word addr s = no_flow_from (ward_region addr) s`;
=======
val mem_region_eq_def = Define`
mem_eq region mema memb = 
   (!x. x IN region ==> ((mema x) = (memb x)))
`

val m0_region_eq_def = Define `
m0_region_eq region s1 s2 = 
   (mem_eq region s1.MEM s2.MEM)
`
DB.find "m0_state"
val m0_non_region_eq_def = Define `
  m0_non_uart_eq s1 s2 = (

(s1.AIRCR = s2.AIRCR)/\
(s1.CCR = s2.CCR)/\
(s1.CONTROL = s2.CONTROL)/\
(s1.CurrentMode = s2.CurrentMode)/\
ExceptionActive
NVIC_IPR
PRIMASK
PSR
REG
SHPR2
SHPR3
VTOR
count
exception
pcinc
pending

   (a.REG = b.REG) /\ (a.count = b.count) /\ (non_uart_mem_eq a.MEM b.MEM)
   (* Do we need to include other parts of the state ?, yes*)
  )
`;

val m0_non_uart_eq_def = Define `
  m0_non_uart_eq a b = (
   (a.REG = b.REG) /\ (a.count = b.count) /\ (non_uart_mem_eq a.MEM b.MEM)
   (* Do we need to include other parts of the state ?, yes*)
  )
`;

val m0_uart_eq_def = Define `
  m0_uart_eq a b = 
    (uart_mem_eq a.MEM b.MEM)
`;


val no_if_uart_2_cpu_def = Define`
no_if_uart_2_cpu s0 = (
    ! s1. m0_non_uart_eq s0 s1 ==> m0_non_uart_eq (Next s0) (Next s1)
)`;

val no_if_cpu_2_uart_def = Define`
no_if_uart_2_cpu s0 = (
    (** we need to fex next instruction to be executed, if code is always located in a fixed region of memory then it would be better to constain that memory region instead **)
    ! s1. (** s1.REG PC = s0.REG PC /\ s0.MEM (R s PC) = s1.MEM(R s' PC) **) => 
         m0_uart_eq s0 s1 ==> m0_uart_eq (Next s0) (Next s1)
)`;

val no_if_2_cpu_no_load_thm = prove (`` !s.  no_if_uart_2_cpu s  ==> ~( load_uart_reg s)``,
STRIP_TAC
EQ_TAC
SIMP_TAC std_ss [no_if_uart_2_cpu_def]
Induct_on `s` 
Induct_on `f1`
);


(** experements to investigate proving information flow for decompiled code **)
val m0_non_addr_eq_def = Define `
  m0_non_uart_eq addr a b = (
   (a.REG = b.REG) /\ (a.count = b.count) /\ 
          (!addr'. (addr' <> addr) ==> ((a.MEM addr')=(b.MEM addr')))
   (* Do we need to include other parts of the state ?*)
  )
`;


val m0_addr_eq_def = Define `
  m0_addr_eq addr a b =
       (** TODO: might need to fix PC, (s.MEM PC) and regesters used by the instruction at s.MEM PC **)
    ((a.MEM addr)=(b.MEM addr))
`;


(** this version without ext.quant. **)
val mem_written_1_def = Define`
    mem_written_1 s a = let
      s'  = s with MEM updated_by (\m. (a =+ 0w) m );  
      s'' = s with MEM updated_by (\m. (a =+ ~0w) m)
    in ~((((Next(s')).MEM a) = 0w) /\ ( ((Next(s'')).MEM a)=~0w)) 
`;

(** this version is more in Information flow style**)


val nif_from_addr_def = Define`
    nif_from_addr a s = !s'. (** TODO: 
                if next operation is fixed!!! ==> **) 
         m0_addr_eq a s s' ==>
             m0_addr_eq a (Next s) (Next s')           
`;

val nif_to_addr_def = Define`
    nif_to_addr a s = !s'. (** TODO: 
                if next operation is fixed!!! ==> **) 
         m0_non_addr_eq a s s' ==>
             m0_non_addr_eq a (Next s) (Next s')           
`;

val if_to_addr_def = Define`
    if_to_addr_def a s = ?s'. (m0_non_addr_eq a s s' ) /\ ~(m0_non_addr_eq a (Next s) (Next s'))
`;
