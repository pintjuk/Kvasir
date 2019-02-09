open HolKernel Parse boolLib;
open boolSimps;
open bossLib;
open wordsTheory;
open m0Theory;
open fcpTheory;
open m0_NITTheory;

val _ = new_theory "uart";

(*********************************)
(*   buffer model                *)
(*********************************)

val _= Datatype `buffer = <| data: word32 ['n];
                              h:num;
                              t:num;
                              Size:num;
                              cap:num; |>`;

val bufferN_def = Define `
Buffer (:'n) = <| data := (FCP i. 0w):word32['n];
                  h:=0; t:=0; Size:= 0;
                  cap:=dimindex(:'n); |>`;

val Pop_def = Define `
Pop  buf =  ((* Result: *)
                (buf.data ' buf.t),
             (* Next  buffer state:*) 
                (buf with <|  t updated_by SUC;  
                                   Size updated_by PRE|>))`;

val Push_def = Define `
Push el buf  =  buf with <| data updated_by ( (buf.h MOD buf.cap) :+ el);
                            h    updated_by SUC ;
                            Size updated_by  SUC ;|>
`;

val  _ = EVAL ``     Buffer (:5)   :> (Push 1w)
                          :> (Push 2w)
                          :> (Push 3w)
                          :> (Push 4w)
                          :> (Push 5w)
                          :> (Push 6w)
                          :> Pop
                          :> \(x,y). y
                          :> Pop``;

(***********************************************)
(*      uart                                   *)
(***********************************************)

val _= Datatype `uart_state = <|enabled: bool; 
				unpredictable:bool;
		                rx_started: bool; 
                                tx_started:bool;
                                RXD: word32;
                                TXD: word32;
                                RXDRDY: bool;
				TXDRDY: bool;
                                PINSELRXD: word32;
                                PINSELTXD:word32;
                                RBUF:6 buffer ;
                                transmit: bool;
                                rxd_cleared: bool;
                                |>`;

val _= Datatype `uart_mmap_reg = 
		    STARTRX|
		    STOPRX|
		    STARTTX|
		    STOPTX|
		    SUSPEND|
		    CTS|
		    NCTS|
		    RXDRDY|
		    TXDRDY|
		    ERROR|
		    RXTO|
		    INTEN|
		    INTENSET|
		    INTENCLR|
		    ERRORSRC|
		    ENABLE|
		    PSELRTS|
		    PSELTXD|
		    PSELCTS|
		    PSELRXD|
		    RXD|
		    TXD|
		    BAUDRATE|
		    CONFIG`;

val _= Datatype `uart_reg_event = LOAD word32 uart_mmap_reg |
                             STORE word32 uart_mmap_reg`;

val _= Datatype `io_event = IE_OUT
                          | IE_IN  word32`;

val nRF51_uart_mmap_def   = Define`
    (nRF51_uart_mmap STARTRX = 0x40002000w) /\
    (nRF51_uart_mmap STOPRX = 0x40002004w)/\
    (nRF51_uart_mmap STARTTX = 0x40002008w)/\
    (nRF51_uart_mmap STOPTX = 0x4000200Cw)/\
    (nRF51_uart_mmap SUSPEND = 0x4000201Cw)/\
    (nRF51_uart_mmap CTS = 0x40002100w)/\
    (nRF51_uart_mmap NCTS = 0x40002104w)/\
    (nRF51_uart_mmap RXDRDY = 0x40002108w)/\
    (nRF51_uart_mmap TXDRDY = 0x4000211Cw)/\
    (nRF51_uart_mmap ERROR = 0x40002124w)/\
    (nRF51_uart_mmap RXTO = 0x40002144w)/\
    (nRF51_uart_mmap INTEN = 0x40002300w)/\
    (nRF51_uart_mmap INTENSET = 0x40002304w)/\
    (nRF51_uart_mmap INTENCLR = 0x40002308w)/\
    (nRF51_uart_mmap ERRORSRC = 0x40002480w)/\
    (nRF51_uart_mmap ENABLE = 0x40002500w)/\
    (nRF51_uart_mmap PSELRTS = 0x40002508w)/\
    (nRF51_uart_mmap PSELTXD = 0x4000250Cw)/\
    (nRF51_uart_mmap PSELCTS = 0x40002510w)/\
    (nRF51_uart_mmap PSELRXD = 0x40002514w)/\
    (nRF51_uart_mmap RXD = 0x40002518w)/\
    (nRF51_uart_mmap TXD = 0x4000251Cw)/\
    (nRF51_uart_mmap BAUDRATE = 0x40002524w)/\
    (nRF51_uart_mmap CONFIG = 0x4000256Cw)`;

val nRF51_uart_mmap'_def   = Define`
    nRF51_uart_mmap' addr=
	if      addr = 0x40002000w  then SOME STARTRX 
	else if addr = 0x40002004w then SOME STOPRX 
	else if addr = 0x40002008w then SOME STARTTX
	else if addr = 0x4000200Cw then SOME STOPTX 
	else if addr = 0x4000201Cw then SOME SUSPEND 
	else if addr = 0x40002100w then SOME CTS 
	else if addr = 0x40002104w then SOME NCTS 
	else if addr = 0x40002108w then SOME RXDRDY 
	else if addr = 0x4000211Cw then SOME TXDRDY 
	else if addr = 0x40002124w then SOME ERROR 
	else if addr = 0x40002144w then SOME RXTO 
	else if addr = 0x40002300w then SOME INTEN 
	else if addr = 0x40002304w then SOME INTENSET 
	else if addr = 0x40002308w then SOME INTENCLR 
	else if addr = 0x40002480w then SOME ERRORSRC 
	else if addr = 0x40002500w then SOME ENABLE 
	else if addr = 0x40002508w then SOME PSELRTS 
	else if addr = 0x4000250Cw then SOME PSELTXD 
	else if addr = 0x40002510w then SOME PSELCTS 
	else if addr = 0x40002514w then SOME PSELRXD 
	else if addr = 0x40002518w then SOME RXD 
	else if addr = 0x4000251Cw then SOME TXD 
	else if addr = 0x40002524w then SOME BAUDRATE 
	else if addr = 0x4000256Cw then SOME CONFIG
	else NONE`;

(*
val nRF51_uart_mmap_def   = Define`
nRF51_uart_mmap =  <|   STARTRX:= 0x40002000w;
			STOPRX:= 0x40002004w;
			STARTTX:= 0x40002008w;
			STOPTX:= 0x4000200Cw;
			SUSPEND:= 0x4000201Cw;
			CTS:= 0x40002100w;
			NCTS:= 0x40002104w;
			RXDRDY:= 0x40002108w;
			TXDRDY:= 0x4000211Cw;
			ERROR:= 0x40002124w;
			RXTO:= 0x40002144w;
			INTEN:= 0x40002300w;
			INTENSET:= 0x40002304w;
			INTENCLR:= 0x40002308w;
			ERRORSRC:= 0x40002480w;
			ENABLE:= 0x40002500w;
			PSELRTS:= 0x40002508w;
			PSELTXD:= 0x4000250Cw;
			PSELCTS:= 0x40002510w;
			PSELRXD:= 0x40002514w;
			RXD:= 0x40002518w;
			TXD:= 0x4000251Cw;
			BAUDRATE:= 0x40002524w;
			CONFIG:= 0x4000256Cw;|>`;


val _= Datatype `uart_mmap = <|
		    STARTRX: word32;
		    STOPRX: word32;
		    STARTTX: word32;
		    STOPTX: word32;
		    SUSPEND: word32;
		    CTS: word32;
		    NCTS: word32;
		    RXDRDY: word32;
		    TXDRDY: word32;
		    ERROR: word32;
		    RXTO: word32;
		    INTEN: word32;
		    INTENSET: word32;
		    INTENCLR: word32;
		    ERRORSRC: word32;
		    ENABLE: word32;
		    PSELRTS: word32;
		    PSELTXD: word32;
		    PSELCTS: word32;
		    PSELRXD: word32;
		    RXD: word32;
		    TXD: word32;
		    BAUDRATE: word32;
		    CONFIG: word32; |> `;
*)

val nRF51_uart_initial_state_def   = Define`
    nRF51_uart_initial_state = <|
        unpredictable:=F;
	enabled:= F; 
	rx_started:= F; 
	tx_started:= F;
	RXD:= 0w;
	TXD:= 0w;
	RXDRDY:=F;
	TXDRDY:=F;
	PINSELRXD:=0w;
	PINSELTXD:=0w;
	RBUF:= (Buffer (:6));
        transmit:=F;
        rxd_cleared:=F;
|>`;

(*
val uart_pop_rbuf_def = Define `
 uart_pop_rbuf uart =
 let
   (r, n) =  Pop uart.RBUF;
 in if n = NONE 
    then  (NONE, NONE)
    else  (r, SOME( uart with RBUF updated_by (\x. THE n)))
`;



val uart_push_rbuf_def = Define `
 uart_push_rbuf w uart =
 let
   (r, n) =  Push w uart.RBUF
 in if n = NONE 
    then  (NONE, NONE)
    else  (r, SOME( uart with RBUF updated_by (\x. THE n)))
`;
*)


(*******************************************)
(*          UART NIF                       *)
(*******************************************)

(* state equevalance *)     
val m0u_r_eq_def = Define `
    m0u_r_eq region ((s1,u1),in1,out1) ((s2, u2),in2,out2)  = 
        m0_r_eq region s1 s2 /\ (u1=u2) /\ (out1=out2) /\ (in1=in2)`;

val m0u_non_r_eq_def = Define `
    m0u_non_r_eq region ((s1,u1),in1,out1) ((s2, u2),in2,out2) = 
        m0_non_r_eq region s1 s2`;

val m0u_m0_non_r_eq_def = Define `
    m0u_m0_non_r_eq region ((s1,u1),in1,out1) s2 = 
        m0_non_r_eq region s1 s2`;

(* state equevalance reflexivity, antisymetry and transitivity *)
val m0u_r_eq_refl_thm = Q.store_thm("m0u_r_eq_refl_thm",
`!region s. m0u_r_eq region s s`,

    Cases_on `s`>>
    Cases_on `r`>>
    Cases_on `q`>>
    METIS_TAC[m0u_r_eq_def, m0_r_eq_refl_thm]
);

val m0u_non_r_eq_refl_thm = Q.store_thm("m0u_non_r_eq_refl_thm",
`!region s. m0u_non_r_eq region s s`,

    Cases_on `s`>>
    Cases_on `r`>>
    Cases_on `q`>>
    METIS_TAC[m0u_non_r_eq_def, m0_non_r_eq_refl_thm]
);

val m0u_r_eq_antisym_thm = Q.store_thm("m0u_r_eq_antisym_thm",
    `!region s1 s2. m0u_r_eq region s1 s2 = m0u_r_eq region s2 s1`,
    Cases_on `s1`>>
    Cases_on `s2`>>
    Cases_on `r`>>
    Cases_on `r'`>>
    Cases_on `q`>>
    Cases_on `q'`>>
    METIS_TAC[m0u_r_eq_def, m0_r_eq_antisym_thm]
);

val m0u_non_r_eq_antisym_thm = Q.store_thm("m0u_non_r_eq_antisym_thm",
    `!region s1 s2. m0u_non_r_eq region s1 s2 = m0u_non_r_eq region s2 s1`,
    Cases_on `s1`>>
    Cases_on `s2`>>
    Cases_on `r`>>
    Cases_on `r'`>>
    Cases_on `q`>>
    Cases_on `q'`>>
    METIS_TAC[m0u_non_r_eq_def, m0_non_r_eq_antisym_thm]);

val m0u_r_eq_trans_thm = Q.store_thm("m0u_r_eq_trans_thm",
    `!region s1 s2 s3. m0u_r_eq region s1 s2 /\ m0u_r_eq region s2 s3 ==> m0u_r_eq region s1 s3`,
    Cases_on `s1`>>
    Cases_on `s2`>>
    Cases_on `s3`>>
    Cases_on `q`>>
    Cases_on `q'`>>
    Cases_on `q''`>>
    Cases_on `r`>>
    Cases_on `r'`>>
    Cases_on `r''`>>
    METIS_TAC[m0u_r_eq_def, m0_r_eq_trans_thm]
);

val m0u_non_r_eq_trans_thm = Q.store_thm("m0u_non_r_eq_trans_thm",
    `!region s1 s2 s3. m0u_non_r_eq region s1 s2 /\ m0u_non_r_eq region s2 s3 ==> m0u_non_r_eq region s1 s3`,
    Cases_on `s1`>>
    Cases_on `s2`>>
    Cases_on `s3`>>
    Cases_on `q`>>
    Cases_on `q'`>>
    Cases_on `q''`>>
    Cases_on `r`>>
    Cases_on `r'`>>
    Cases_on `r''`>>
    METIS_TAC[m0u_non_r_eq_def, m0_non_r_eq_trans_thm]);

val ward_region_def = Define`
(* TODO: change to bit masking? *)
ward_region (x:word32) = {x;x+1w; x+2w;x+3w}
`;

val uart_r_def = Define`
uart_r=(ward_region(nRF51_uart_mmap STARTRX) UNION
ward_region(nRF51_uart_mmap STOPRX) UNION
ward_region(nRF51_uart_mmap STARTTX) UNION
ward_region(nRF51_uart_mmap STOPTX) UNION
ward_region(nRF51_uart_mmap SUSPEND) UNION
ward_region(nRF51_uart_mmap CTS) UNION
ward_region(nRF51_uart_mmap NCTS) UNION
ward_region(nRF51_uart_mmap RXDRDY) UNION
ward_region(nRF51_uart_mmap TXDRDY) UNION
ward_region(nRF51_uart_mmap ERROR) UNION
ward_region(nRF51_uart_mmap RXTO) UNION
ward_region(nRF51_uart_mmap INTEN) UNION
ward_region(nRF51_uart_mmap INTENSET) UNION
ward_region(nRF51_uart_mmap INTENCLR) UNION
ward_region(nRF51_uart_mmap ERRORSRC) UNION
ward_region(nRF51_uart_mmap ENABLE) UNION
ward_region(nRF51_uart_mmap PSELRTS) UNION
ward_region(nRF51_uart_mmap PSELTXD) UNION
ward_region(nRF51_uart_mmap PSELCTS) UNION
ward_region(nRF51_uart_mmap PSELRXD) UNION
ward_region(nRF51_uart_mmap RXD) UNION
ward_region(nRF51_uart_mmap TXD) UNION
ward_region(nRF51_uart_mmap BAUDRATE) UNION
ward_region(nRF51_uart_mmap CONFIG))`;


(*
this theorem does not hold sincethere are gaps in uart registers right now 

``uart_r = {addr| addr >= 0x40002000w /\ addr <= (0x4000256Cw+3w)}``


ASM_SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss++wordsLib.WORD_LOGIC_ss  ) [FUN_EQ_THM, uart_r_def, ward_region_def, nRF51_uart_mmap_def] 


REPEAT STRIP_TAC>>


val tactic1 = (fn x => 
Cases_on (`x:word32 = `@[QUOTE ((Int.toString x)^"w:word32")])
>- (ASM_SIMP_TAC std_ss []>> blastLib.FULL_BBLAST_TAC )
)
fun tactical1 a b = if a=b 
    then tactic1 a >> (PAT_X_ASSUM ``_`` MP_TAC) 
    else (tactic1 a >> 
          (PAT_X_ASSUM ``_`` MP_TAC) >>
          (tactical1 (a+1) b))		   

tactical1 (0x40002000) (0x4000200f)

*)


(*******************************************)
(*          NEXT function                  *)
(*******************************************)

val uart_next_cpu_def = Define`
    uart_next_cpu event uart = 
         case event of
	     STORE w STARTRX => if uart.enabled 
                                then SOME (uart with <|rx_started:=T|>)
                                else SOME uart 
		   |STORE w STOPRX => if uart.enabled 
                                      then SOME (uart with <|rx_started:=F|>)
                                      else SOME uart
		   |STORE w STARTTX =>if uart.enabled 
                                      then SOME (uart with <|tx_started:=T|>)
                                      else SOME uart
		   |STORE w STOPTX => if uart.enabled 
                                      then SOME (uart with <|tx_started:=F|>)
                                      else SOME uart
		   |STORE w SUSPEND => NONE
		   |STORE w CTS => NONE
		   |STORE w NCTS => NONE
                     (* Need to test how this actually works, will any wright clear the register, or is it only 0w that does it, what if the CPU wrights something different then r0*)
		   |STORE w RXDRDY => if w=0w then SOME (uart with <|RXDRDY:=F|>)
                                              else NONE
		   |STORE w TXDRDY => if w=0w then SOME (uart with <|TXDRDY:=F|>)
                                              else NONE
		   |STORE w ERROR => NONE
		   |STORE w RXTO => NONE
		   |STORE w INTEN => NONE
		   |STORE w INTENSET => NONE
		   |STORE w INTENCLR => NONE
		   |STORE w ERRORSRC => NONE
		   |STORE w ENABLE => SOME (uart with  <|enabled:=T|>)
		   |STORE w PSELRTS => NONE 
		   |STORE w PSELTXD => NONE
		   |STORE w PSELCTS => NONE
		   |STORE w PSELRXD => NONE
		   |STORE w RXD => NONE
		   |STORE w TXD => if uart.transmit 
                                   then NONE
                                   else SOME (uart with <|TXD:=w; transmit:=T|>)
		   |STORE w BAUDRATE => NONE
		   |STORE w CONFIG => NONE
		   |LOAD w STARTRX => NONE
		   |LOAD w STOPRX => NONE
		   |LOAD w STARTTX => NONE
		   |LOAD w STOPTX => NONE
		   |LOAD w SUSPEND => NONE
		   |LOAD w CTS => NONE
		   |LOAD w NCTS => NONE
		   |LOAD w RXDRDY => SOME ( uart with <|rxd_cleared:=T|> )
		   |LOAD w TXDRDY => SOME uart
		   |LOAD w ERROR => NONE
		   |LOAD w RXTO => NONE
		   |LOAD w INTEN => NONE
		   |LOAD w INTENSET => NONE
		   |LOAD w INTENCLR => NONE
		   |LOAD w ERRORSRC => NONE
		   |LOAD w ENABLE => NONE
		   |LOAD w PSELRTS => NONE
		   |LOAD w PSELTXD => NONE
		   |LOAD w PSELCTS => NONE
		   |LOAD w PSELRXD => NONE
		   |LOAD w RXD => NONE
		   |LOAD w TXD => NONE
		   |LOAD w BAUDRATE => NONE
		   |LOAD w CONFIG => NONE
`;

(*
uart_next_io_def = Define `
    uart_next_io (input:word32 option) uart =
        case input of 
            NONE => if uart.transmit 
                    then (SOME uart.TXD, uart with <| TXD:=0w;  
                                                      transmit:=F; 
                                                      TXDRDY:=T|>)
                    else (NONE, uart)   
          | SOME w => (NONE, uart)

)`;
*)

val m0u_Next_def= Define 
`m0u_Next (((s:m0_state), (u:uart_state)), (input:word32 list), (output:word32 list)) =  
    if NIT_STEP uart_r s
    then     ((Next s,u) ,input, output)
    else  
(*** IMPLEMENT the actual model
**)
((ARB, ARB), ARB, ARB)`

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

(********************************************)
(*           Uart model theorems            *)
(*                                          *)
(********************************************)

val AXI = Q.store_thm("AXI", 
`!s_m0 s_m0u.  
(NIT_STEP uart_r s_m0) /\ (m0u_m0_non_r_eq uart_r s_m0u s_m0 ) ==>
             (m0u_m0_non_r_eq uart_r (m0u_Next s_m0u) (Next s_m0))/\
             (m0u_r_eq uart_r (m0u_Next s_m0u) s_m0u)`,

    REPEAT GEN_TAC>> 
    Cases_on `s_m0u`>>
    rename1  `m0u_m0_non_r_eq uart_r (s_m0u,io) s_m0`>>
    Cases_on `io` >>
    rename1 `(m0u_Next (s_m0u,input,output))`>>
    Cases_on `s_m0u`>>
    SIMP_TAC (std_ss++LET_ss) [m0u_Next_def, m0u_r_eq_def ,m0u_m0_non_r_eq_def, PULL_FORALL, NIT_STEP_TRANS_thm, NIT_STEP_TRANS_thm]>>
    
    METIS_TAC[
NIT_STEP_TRANS_thm, m0_non_r_eq_antisym_thm,
        m0_non_r_eq_antisym_thm,
	m0_r_eq_antisym_thm, m0u_m0_non_r_eq_def,
	m0u_r_eq_def, NIT_STEP_thm]
);

val _ = export_theory();
