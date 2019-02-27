open HolKernel Parse boolLib bossLib;
open stateTheory m0_stepTheory boolSimps;
open wordsTheory;
open m0Theory;
open boolSimps;
open optionTheory;
open m0_progLib;
open m0_progTheory;
open progTheory;

val _ = new_theory "m0_NIT";


(* Memory region equality
   region is a set of addresses
*)
val mem_eq_def = Define`
mem_eq region mem1 mem2 = 
   (!x. x IN region ==> ((mem1 x) = (mem2 x)))
`;

(* States are equal in the given memory region*)
val m0_r_eq_def = Define `
m0_r_eq region s1 s2 = 
   (mem_eq region s1.MEM s2.MEM)
`;

(* States are equevilent except for the given memery region*)
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
    That is, next instruction does not write to the region
**)
val NIT_STEP_to_def = Define` 
 NIT_STEP_to region s = (
  !s'.  m0_non_r_eq region s s' ==> m0_r_eq region s' (Next s') 
)`;

(** There is no information flow to the rest of the state from this region 
    During the next tranisition 
    That is, next instruction does not write to the region.
**)
val NIT_STEP_from_def = Define` 
 NIT_STEP_from region s = (
  !s'. m0_non_r_eq region s s'==> m0_non_r_eq region (Next s) (Next s') 
)`;


(* There is no flow to or from the region during the execution of next instruction.
   That is next instruction nether writs nor reads during the next step
*)
val NIT_STEP_def = Define`
NIT_STEP region s = (NIT_STEP_from region s) /\ (NIT_STEP_to region s) 
`;

val NIT_STEP_thm = Q.store_thm ("NIT_STEP_thm",
    `!region s. NIT_STEP region s =  
         (!s'. m0_non_r_eq region s s'==> 
            (m0_non_r_eq region (Next s) (Next s') /\
             m0_r_eq region s' (Next s')))`,
    SIMP_TAC std_ss [NIT_STEP_def, NIT_STEP_to_def, NIT_STEP_from_def]>>
    METIS_TAC []
);


(* This is our week non interference property
   No information flow can be observed after executing T clock cycles, 
   from a state constrained by P
*)
val NIT_W_def = Define`
NIT_W region P t =   !s s' seq seq' i.   
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               m0_non_r_eq region s s' /\ 
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
               ((seq i).count = s.count+t)) ==>   
                   m0_non_r_eq region (seq i) (seq' i) /\
                   m0_r_eq region s' (seq' i)`;

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

(*
val NIT_SS_def = Define`
!region P t. NIT_SS region(P :(m0_component # m0_data -> bool) -> bool)  t =   !s s' seq seq' i.   
               ((SEP_REFINE (P * SEP_T) ($=) (STATE m0_proj) s) /\
               m0_non_r_eq region s s' /\ 
               rel_sequence (NEXT_REL $= NextStateM0) seq  s /\
               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
               ((seq (SUC i)).count <= s.count+t)) ==>   
                   m0_non_r_eq region (seq (SUC i)) (seq' (SUC i)) /\
                   m0_r_eq region (seq' i) (seq' (SUC i))`;

val NIT_SS_thm = store_thm("NIT_NIT_SS_thm", 
``! reg P t. NIT reg P t ==>  NIT_SS reg P t``,

    fs[NIT_def,NIT_SS_def, rel_sequence_def]>>
    REPEAT strip_tac>>
    Induct_on  `i`>> fs[]>-(
        Q.PAT_X_ASSUM `! seq seq' i . _ `  ( MP_TAC o (Q.SPECL [`seq`,`seq'`,`1`]))>>
        METIS_TAC[]
    )>>
    
    Q.PAT_ASSUM `! seq seq' i . _ `  ( MP_TAC o (Q.SPECL [`seq`,`seq'`,`SUC (SUC i)`]))>>
    Q.PAT_X_ASSUM `! seq seq' i . _ `  ( MP_TAC o (Q.SPECL [`seq`,`seq'`,`i`]))>>
    `(seq (SUC i)).count ≤ t + (seq 0).count` by cheat>>
    `(seq i).count ≤ t + (seq 0).count` by cheat>>
    fs[]>>
    METIS_TAC[m0_r_eq_trans_thm,  m0_r_eq_antisym_thm ]
   );


NIT_STEP_thm
    
``∀region s.
         NIT_STEP region s ⇔
         ∀s'.
             rel_sequence (NEXT_REL $= NextStateM0) seq  s /\

               rel_sequence (NEXT_REL $= NextStateM0) seq' s' /\
             m0_non_r_eq region s s' ⇒
             m0_non_r_eq region (Next s) (Next s') ∧
             m0_r_eq region s' (Next s')``
*)
(********************************)
(*   uart eqvivalance thearems  *)
(********************************)


(* transitive, reflexiv and antisymetric properties of my
 of state equevalance relations *)
val mem_eq_refl_thm = Q.store_thm("mem_eq_refl_thm",
    `!region mem. mem_eq region mem mem `,
	 METIS_TAC[mem_eq_def]
);
val mem_eq_antisym_thm = Q.store_thm("mem_eq_antisym_thm",
    `!region mem1 mem2. 
	(mem_eq region mem1 mem2)  = (mem_eq region mem2 mem1) `,
	 METIS_TAC[mem_eq_def]
);

val mem_eq_trans_thm = Q.store_thm("mem_eq_trans_thm",
    `!region mem1 mem2 mem3. 
	(mem_eq region mem1 mem2) /\ 
	(mem_eq region mem2 mem3) ==>
	    (mem_eq region mem1 mem3) `,
SIMP_TAC std_ss [mem_eq_def]);

val m0_r_eq_refl_thm = Q.store_thm ("m0_r_eq_refl_thm",
`!s region. m0_r_eq region s s `,
SIMP_TAC std_ss [m0_r_eq_def, mem_eq_refl_thm]);

val m0_non_r_eq_refl_thm = Q.store_thm ("m0_non_r_eq_refl_thm",
`!s region. m0_non_r_eq region s s`,
SIMP_TAC std_ss [m0_non_r_eq_def, mem_eq_refl_thm]>>
METIS_TAC [mem_eq_refl_thm]
);

val m0_r_eq_antisym_thm = Q.store_thm ("m0_r_eq_antisym_thm",
`!s1 s2 region. m0_r_eq region s1 s2 =  m0_r_eq region s2 s1`,
SIMP_TAC std_ss [m0_r_eq_def, mem_eq_antisym_thm]);

val m0_non_r_eq_antisym_thm = Q.store_thm ("m0_non_r_eq_antisym_thm",
`!s1 s2 region. m0_non_r_eq region s1 s2 =  m0_non_r_eq region s2 s1`,
SIMP_TAC std_ss [m0_non_r_eq_def, mem_eq_antisym_thm]>>
METIS_TAC [mem_eq_refl_thm]
);

val m0_non_r_eq_trans_thm = Q.store_thm ("m0_non_r_eq_trans_thm",
`!s1 s2 s3 region.
    m0_non_r_eq region s1 s2 /\
    m0_non_r_eq region s2 s3 ==>
        m0_non_r_eq region s1 s3`,
REPEAT GEN_TAC>>
SIMP_TAC std_ss [m0_non_r_eq_def]>>
METIS_TAC[ mem_eq_trans_thm]);

val m0_r_eq_trans_thm = Q.store_thm ("m0_r_eq_trans_thm",
`!s1 s2 s3 region.
    m0_r_eq region s1 s2 /\
    m0_r_eq region s2 s3 ==>
        m0_r_eq region s1 s3`,
REPEAT GEN_TAC>>
SIMP_TAC std_ss [m0_r_eq_def]>>
METIS_TAC[ mem_eq_trans_thm]);

(*******************************************************)
(*            NIT theorems                             *)
(*******************************************************)


val NIT_STEP_TRANS_thm = Q.store_thm("NIT_STEP_TRANS_thm",
`!r s q . NIT_STEP r s ∧ m0_non_r_eq r q s ==> NIT_STEP r q`,
SIMP_TAC std_ss [ NIT_STEP_thm]>>
    METIS_TAC [m0_non_r_eq_trans_thm, m0_non_r_eq_antisym_thm ]);
(*
val NIF_STEP_to_UNION_thm = Q.store_thm ("NIF_STEP_to_UNION_thm",
    `! s region1 region2. NIT_STEP_to region1 s  /\ NIT_STEP_to region2 s ==> 
                          NIT_STEP_to (region1 UNION region2) s`,
    cheat
    (*
    the idea was to do a conterposition prof

    SIMP_TAC std_ss [PULL_FORALL, NIT_STEP_def, NIT_STEP_to_def, NIT_STEP_from_def]>>
	     REPEAT STRIP_TAC>>
	     Q.PAT_X_ASSUM `!a b._` (MP_TAC o Q.SPECL [`s'`, `s'`])>>
	     REPEAT STRIP_TAC
	     
    Cases_on `m0_r_eq (region1 ∪ region2) s' (Next s')`>>ASM_SIMP_TAC std_ss []

    nagate the conscusions 
    ` ~ m0_r_eq region1 s' (Next s')` by cheat
    ` ~ m0_r_eq region2 s' (Next s')` by cheat
    and get negation of assumptions

    `~(m0_non_r_eq region1 s s')` by METIS_TAC []
    `~(m0_non_r_eq region2 s s')` by METIS_TAC []

    and then show the contradiction
   REPEAT ( Q.PAT_X_ASSUM `_==>_` (fn x=> ALL_TAC))
   REPEAT ( PAT_X_ASSUM ``~ m0_r_eq _ _ (Next s')`` (fn x=> ALL_TAC))
   ( PAT_X_ASSUM ``_`` MP_TAC)
   REWITE_TAC []

   ONCE_SIMP_TAC (std_ss) [m0_non_r_eq_def]
   
   def_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [m0_non_r_eq_def, mem_eq_def, PULL_EXISTS, PULL_FORALL]
   REPEAT STRIP_TAC
   
   PAT_ASSUM ``!x._`` (MP_TAC o (Q.SPEC `x'`))>>
   PAT_ASSUM ``!x._`` (MP_TAC o (Q.SPEC `x`))
   
   *)
);

val NIF_STEP_from_UNION_thm = Q.store_thm ("NIF_STEP_from_UNION_thm",
    `! s region1 region2. NIT_STEP_from region1 s  /\ NIT_STEP_from region2 s ==> 
                          NIT_STEP_from (region1 UNION region2) s`,
    cheat
);

val NIF_STEP_UNION_thm = Q.store_thm ("NIF_STEP_UNION_thm",
    `! s region1 region2. NIT_STEP region1 s  /\ NIT_STEP region2 s ==> 
                          NIT_STEP (region1 UNION region2) s`,
    cheat
);
*)


(*****************************)
(*   Run & equance stuff     *)
(*****************************)


val M0_SEQUENCE_THM = prove(``
  !seq s. rel_sequence (NEXT_REL $= NextStateM0) seq s <=>
  (seq 0 = s) ∧ !n. if (Next(seq n)).exception = NoException 
                    then seq (n+1) = Next (seq n)
                    else seq (n+1) = seq n``,
                            
    SIMP_TAC (std_ss++boolSimps.LET_ss++boolSimps.COND_elim_ss) [
	DECIDE ``SUC n = n + 1n``, rel_sequence_def, NEXT_REL_EQ, NextStateM0_def]>>
    METIS_TAC[]);

val RunM0_def = Define `(RunM0 s 0n = s) /\
                         (RunM0 s k = let 
                           s' = RunM0 s (k-1)
                        in if (Next (s')).exception = NoException 
                           then Next(s')
                           else s')`;


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
);


val SEQUENCE_EXISTS_THM = Q.store_thm(
    "SEQUENCE_EXISTS_THM",
    `!s. ?seq. (rel_sequence (NEXT_REL $= NextStateM0) seq s)`,
	STRIP_TAC>>
	Q.EXISTS_TAC `RunM0 s`>>
	SIMP_TAC std_ss [RunM0_SEQUENCE_THM]);



(* UART specific shite*)
val uart_region_def = Define`
uart_region = {addr| addr >= 0x40002000w /\ addr <= 0x4000256Cw}
`;
(*

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
*)
val _ = export_theory();
