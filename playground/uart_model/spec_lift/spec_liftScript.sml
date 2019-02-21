 (* set_trace "simplifier" 0; *)

open HolKernel Parse boolLib bossLib;
open uartTheory;
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

val _ = new_theory "spec_lift";

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
val m0_MEM_DOM_thm = store_thm("m0_MEM_DOM_thm",``(DOM (m0_MEM a b)) = {m0_c_MEM a}``,
fs[m0_MEM_def, DOM_def] 
);

val m0_MEM_UART_DISJOINT_thm = store_thm("m0_MEM_UART_DISJOINT_thm",
    ``a NOTIN uart_r <=> ( DISJOINT (DOM (m0_MEM a b)) UART)``,
fs[m0_MEM_DOM_thm, UART_def, r2m0_c_set_def, uart_r_def]
);
val m0_MEMORY_DOM_thm = store_thm("m0_MEMORY_DOM_thm",``(DOM (m0_MEMORY dm m)) = {m0_c_MEM c| c IN dm}``,
    fs[m0_MEMORY_def, m0_MEM_def,DOM_def, FST]>>
    REWRITE_TAC [FUN_EQ_THM] >> STRIP_TAC>>
    EQ_TAC>|[
        fs[]>>STRIP_TAC>>
          Q.EXISTS_TAC `c` >> fs[]
    ,
            fs[]>>STRIP_TAC>>
        Q.EXISTS_TAC `(x, m0_d_word8 (m c))`>> fs[] >>
        Q.EXISTS_TAC `{(m0_c_MEM c,m0_d_word8 (m c))}`>> fs[]
    ]
);

val m0_MEMORY_UART_DISJOINT_thm = store_thm("m0_MEMORY_UART_DISJOINT_thm",
    ``(DISJOINT dm uart_r) <=> ( DISJOINT(DOM (m0_MEMORY dm m)) UART)``,
fs[GEN_ALL m0_MEMORY_DOM_thm, UART_def, r2m0_c_set_def, m0_component_11, uart_r_def, ward_region_def]

);


val m0_REG_DOM_thm = store_thm("m0_REG_DOM_thm",``(DOM (m0_REG a b)) = {m0_c_REG a}``,
fs[m0_REG_def, DOM_def] 
);

val m0_REG_UART_DISJOINT_thm = store_thm("m0_REG_UART_DISJOINT_thm",
    ``DISJOINT (DOM (m0_REG k v)) UART``,
    fs[m0_REG_DOM_thm , UART_def, r2m0_c_set_def]);


val m0_STAR_UART_DISJOINT_thm = store_thm("m0_REG_UART_DISJOINT_thm",
    ``((DOM (A*B)) INTER UART = {})<=> (((DOM (A)) INTER UART = {}) /\ ((DOM (B)) INTER UART = {}))``,cheat);

 val m0_MEMORY_UART_DIFF_DISJOINT_thm = store_thm("m0_MEMORY_DIFF_UART_DISJOINT_thm",
    ``((DOM (m0_MEMORY (dm DIFF uart_r) m)) INTER UART = {})``,cheat);

val m0_MEMORY_SPLIT_thm = store_thm("m0_MEMORY_SPLIT_thm", 
    `` m0_MEMORY dm m = (m0_MEMORY (dm DIFF s) m) *  (m0_MEMORY s m)``,cheat);


(** update subdomain of function **)

val dupdate_def = Define`
dupdate dm new old = (\x. if x IN dm then (new x) else (old x))`;

val m0_MEMORY_UPDATE_MEM_SELECT_thm = store_thm("m0_MEMORY_UPDATE_MEM_SELECT_thm",``(m0_MEMORY dm m)(SELECT_STATE m0_proj (r2m0_c_set dm) (s with MEM updated_by dupdate dm m))``,cheat);

val m0_MEMORY_UPDATE_MEM_SELET_UART_thm = store_thm("m0_MEMORY_UPDATE_MEM_SELET_UART_thm",
``(m0_MEMORY uart_r m)(SELECT_STATE m0_proj (UART) (s with MEM updated_by dupdate uart_r m))``, 
fs[ m0_MEMORY_UPDATE_MEM_SELECT_thm,UART_def]);



val m0u_m0_non_r_eq_invariant = store_thm("m0u_m0_non_r_eq_invariant", 
``m0u_m0_non_r_eq uart_r (state:((m0_state # uart_state) # word32 list # word32 list)) (((state:>FST:>FST)with MEM updated_by dupdate uart_r m ) )``, cheat);


val m0u_UART_def = Define` m0u_UART =  IMAGE m0_c UART`;

val sep_expr_split = store_thm("sep_expr_split",
`` !(F :(m0u_component # m0u_data -> bool) -> bool) .?F_r F_u. (F  = (F_r * F_u) )/\ ( (DOM F_u) SUBSET m0u_UART) /\ ( (DOM F_r) SUBSET (COMPL m0u_UART))``,
cheat);

val existsy_m0_prop = store_thm("exists_m0_prop",
`` 
 !F_r. ( (DOM F_r) SUBSET (COMPL m0u_UART)) ==> ?F'_r. F_r = TO_M0U_PROP F'_r

``,
cheat);

val seq_exists = prove(``!s .?seq. rel_sequence (NEXT_REL $= NextStateM0) seq s``,
                       cheat
);
(*
``SPEC M0_MODEL (P* m0_MEMORY uart_r m *(m0_count t0))  code (Q*m0_MEMORY uart_r m' * m0_count (t0+t))/\ 
        (cosim (P* m0_MEMORY uart_r m *(m0_count t0)) code t) /\
(DISJOINT (DOM P) UART)/\
(DISJOINT (DOM Q) UART) ==> 
(SPEC M0U_MODEL (TO_M0U_PROP (P * m0_count t0)) code (TO_M0U_PROP(Q * m0_count (t0+t))))
``,


    fs [ SPEC_def, M0U_MODEL_def, M0_MODEL_def, RUN_def , SEP_REFINE_def, STATE_def]>>
    STRIP_TAC>>
    REPEAT GEN_TAC>> 
    rename1 `(CODE_POOL m0u_instr code * TO_M0U_PROP (P * m0_count t0) * r)
            (SELECT_STATE m0u_proj 𝕌(:m0u_component)  s0') `>>

    REPEAT STRIP_TAC >>
    rename1 `rel_sequence (NEXT_REL $= NextStateM0U) seq' s0'`>>
    MP_TAC ( m0u_m0_non_r_eq_invariant |> GEN_ALL |> Q.SPECL [`s0'`, `m`])>>
    Q.ABBREV_TAC `s_0 = ((s0' :> FST :> FST) with MEM updated_by dupdate uart_r m)` >>
    strip_tac>>
    mp_tac ( 
        sep_expr_split |> (Q.SPECL [` (r :(m0u_component # m0u_data -> bool) -> bool)`]))>>
   
    STRIP_TAC>>

    MP_TAC (existsy_m0_prop|> Q.SPECL [`F_r`]) >> fs[]>> STRIP_TAC>>
    Q.PAT_X_ASSUM  `!state r._` (MP_TAC o Q.SPECL[`s_0`, `F'_r * SEP_T`] )>>
    strip_tac>>

   `(CODE_POOL m0_instr code * (P * m0_MEMORY uart_r m * m0_count t0) *
          (F'_r * SEP_T)) (SELECT_STATE m0_proj 𝕌(:m0_component) s_0)` by cheat>>
    fs[]>>
    MP_TAC (seq_exists|> Q.SPECL [`s_0`])>>strip_tac>>
    Q.PAT_X_ASSUM  `!seq._` (MP_TAC o Q.SPECL[`seq`] )>> fs[]>>
    strip_tac>>
    Q.EXISTS_TAC `i`>>

    `(s0).count= t` by cheat >>
    `(seq i).count= t+t0` by cheat >>
    `(seq i).count=s0.count+t`by cheat>>
  Q.PAT_X_ASSUM `cosim _ _ _` (MP_TAC o Q.SPECL [`s0`, `s0'`, `seq`, `seq'`, `i`] 
                                      o  SIMP_RULE std_ss [cosim_def,COSIM_def]   )>>
   fs[SEP_REFINE_def] 

   Q.SPECL [`p`,`b`,`(STATE m0_proj s0)`] ( prove(``!p b s. ( p * b) s  ==> (p * SEP_T) s``, cheat))
  
*)
val _ = export_theory();
