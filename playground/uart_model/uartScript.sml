loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/model"::(!loadPath));
loadPath := ("/Home/daniil/HOL/examples/l3-machine-code/common"::(!loadPath));
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));
open  wordsTheory;
open m0Theory;
open m0_decompLib;
open fcpTheory;


val _ = new_theory "uartModel";

(*

DB.find "Next"
DB.find "SEP_REFINE_def"
DB.find "SPEC_def"
DB.find "m0_MODEL"

DB.find  "STATE_def"
DB.find  "CODE_POOL"
DB.find  "m0_instr"

DB.match ["m0_prog"] ``_``

DB.find "m0_state_typedef"
DB.find "m0_state_induct"
*)


(*********************************)
(*   buffer model                *)
(*********************************)
val _= Datatype `buffer = <| data: word32 ['n];
                              h:num;
                              t:num;
                              size:num;
                              cap:num; |>`;

val bufferN_def = Define `
Buffer (:'n) = <| data := (FCP i. 0w):word32['n];
                  h:=0; t:=0; size:= 0;
                  cap:=dimindex(:'n); |>`;

val Pop_def = Define `
Pop  buf =  ((* Result: *)
                (buf.data ' buf.t),
             (* Next  buffer state:*) 
                (buf with <|  t updated_by SUC;  
                                   size updated_by PRE|>))`;

val Push_def = Define `
Push el buf  =  buf with <| data updated_by ( (buf.h MOD buf.cap) :+ el);
                            h    updated_by SUC ;
                            size updated_by  SUC ;|>
`;

val option_fapply2 = Define `
((ofap f  NONE) = NONE) /\
((ofap f (SOME x)) = (f x))
`;

val option_fapply2 = Define `
((A f (out0, NONE)) = (out0,NONE)) /\
((A f (out0, SOME x)) = let
    (out1, next) = f x;
in if out1 = NONE 
   then  (out0, next)
   else  ([THE out1] ++ out0, next))  `;

EVAL ``     Buffer (:5)   :> (Push 1w)
                          :> (Push 2w)
                          :> (Push 3w)
                          :> (Push 4w)
                          :> (Push 5w)
                          :> (Push 6w)
                          :> Pop
                          :> \(x,y). y
                          :> Pop``

val option_testbuffer = Define  `testbuf= <| data:=[0w;1w;2w;3w];cap:=6|>`;

(***********************************************)
(*      uart                                   *)
(***********************************************)

val _= Datatype `uart_state = <|enabled: bool; 
		                rx_started: bool; 
                                tx_started:bool;
                                RXD: word32;
                                TXD: word32;
                                RXDRDY: bool;
				TXDRDY: bool;
                                PINSELRXD: word32;
                                PINSELTXD:word32;
                                RBUF:'n buffer ;
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


uart_next_io_def = Define `
    uart_next_io (input:word32 option) uart =
        case input of 
            NONE => if uart.transmit 
                    then (SOME uart.TXD, uart with <| TXD:=0w;  
                                                      transmit:=F; 
                                                      TXDRDY:=T|>)
                    else (NONE, uart)   
          | SOME w => (NONE, uart)

)`


(* TODO *)
val load_uart_register_def = Define`
load_uart_register uart reg (cpu:m0_state) = cpu
`;

(* TODO *)
val addres_def = Define`
addres n m state = let 
    (v,s) = case m of
                immediate_form imm32 => (imm32, state)
              | register_form m =>
                  Shift (R m state,SRType_LSL,0,state.PSR.C) state 

(** Model definition using Fetch-Decode to detect transition type  **)
(* TODO: finissh definiton *)
val cpu_next_def Define`
   cpu_next cpu uart = in
     ( v, s ) = Fetch cpu;
     ( v, s ) = Decode v s;
   let case s of
     Load  (LoadWord  ( t, n, m)) => case nRF51_uart_mmap' (addres n m cpu) of
                                        NONE => ( SOME (next cpu), SOME uart )
                                        SOME reg =>  ( (* load cpu register*) SOME (next cpu ), uart_next_cpu (LOAD reg) uart )

     Store (StoreWord ( t, n, m)) => case nRF51_uart_mmap' (addres n m cpu) of
                                        NONE => ( SOME (next cpu), SOME uart )
                                        SOME reg =>  ( SOME (next cpu ), uart_next_cpu (STORE reg) uart )
     Data a => (SUME (next cpu), SEME uart) 
     w => (NONE, NONE) 
`;

(** Model using information flow to detect transition type **)

val is_uart_reg_addr_def = Define`
(* TODO: change to bit masking? *)
is_uart_reg_addr (addr:'a word) = (addr >= 0x40002000w /\ addr <= 0x4000256Cw)
`;

(*
val load_uart_reg_def = Define `
load_uart_reg s = let
    ( v, s) = Fetch s;
    ( v, s) = Decode v s;
in ?t n m. (v  = Load  (LoadWord  ( t, n, m))) /\
    ( is_uart_reg_addr (addres n m s) )
(* TODO: extend to cover other loads eg load type *)
`;


val load_uart_reg2_def = Define `
(*not sure if cases or exists is better*)
load_uart_reg2 s = let
    ( v, s) = Fetch s;
    ( v, s) = Decode v s;
in case v of 
    (Load  (LoadWord  ( t, n, m))) => ( is_uart_reg_addr (addres n m s) )
   |x => F
`; *)

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



val m0_non_uart_eq_def = Define `
  m0_non_uart_eq s1 s2 = (m0_non_r_eq uart_region s1 s2)
`;


(** There is no flow to a memory region from the rest of the state 
    During the next tranisition

    for arbitrary content of the region, the next instruciton does not change the content of the region
**)
val no_flow_to_def = Define` 
 no_flow_to region s = (
  !s'. m0_non_r_eq region s s' ==> m0_r_eq region s' (Next s') 
 )`;

(** There is no information flow to the rest of the state from this region 
    During the next tranisition 
    
    Swaping out the content of the region arbitraraly does not affect the execution of the rest of the state.
**)
val no_flow_from_def = Define` 
 no_flow_from region s = (
  !s'. m0_non_r_eq region s s' ==> m0_r_eq region (Next s) (Next s') 
 )`;




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
