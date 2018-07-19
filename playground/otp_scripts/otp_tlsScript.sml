open HolKernel Parse boolLib bossLib

open wordsLib;
open combinTheory;
open listTheory;

open wordsTheory;

val _ = new_theory "otp_tls"


val _ = type_abbrev("byte", ``:bool[8]``);
(* val _ = type_abbrev("otp_buffer", ``:byte list``); *)
val _ = type_abbrev("otp_input_stream", ``:byte list``);
val _ = type_abbrev("otp_key_stream", ``:num -> byte``);
val _ = type_abbrev("otp_output_stream", ``:byte list``);

val _ = type_abbrev("otp_buffer", ``:num -> byte``);

Datatype `otp_state = <| Buffer :otp_buffer; CurrSeq :num; 
                       In :otp_input_stream; Out :otp_output_stream; Key :otp_key_stream|>`


val max_seq_def = Define `max_seq :num = 16383`;

!s. s.CurrSeq = max_seq - 1 ==>
  s.CurrSeq =tls_otp_spec(s).Curseq /\
  s.Out = tls_otp_spec(s).Out
 
!s s.CurrSeq <= tls_otp_spec(s).CurrSeq


val buffer_def = Define `buffer (n :num) = case n of
                  | 0 => (0w :byte)
		  | 1 => 0w
		  | 2 => 0w
		  | 3 => 0w
		  | 4 => 0w
		  | 5 => 0w
		  | 6 => 0w
		  | 7 => 0w
		  | 8 => 0w
		  | 9 => 0w
		  | _ => ARB`       

val shift_buffer_def = Define `shift_buffer (f : num->byte) :num->byte = 
                         ((0 =+ f 1) 
			 ((1 =+ f 2) 
                         ((2 =+ f 3) 
                         ((3 =+ f 4) 
                         ((4 =+ f 5) 
                         ((5 =+ f 6) 
                         ((6 =+ f 7) 
                         ((7 =+ f 8) 
			 ((8 =+ f 9) 
			 ((9 =+ (0w :byte)) f))))))))))`;

val put_val_in_buf_def = Define `put_val_in_buf (f : num->byte) (b :byte) =
                         ((9 =+ b) f)`;

val uart_read_def = Define `uart_read in_stream = HD in_stream`;

val uart_read_def = Define `(uart_read [] = ARB) /\ (uart_read (x::xs) = x)`

val valid_def = Define `valid (buf :otp_buffer) :bool =
                       (word_msb (buf 0) = T) /\
                       (word_msb (buf 1) = T) /\
                       (word_msb (buf 2) = F) /\
                       (word_msb (buf 3) = F) /\
                       (word_msb (buf 4) = F) /\
                       (word_msb (buf 5) = F) /\
                       (word_msb (buf 6) = F) /\
                       (word_msb (buf 7) = F) /\
                       (word_msb (buf 8) = F) /\
                       (word_msb (buf 9) = F)`;


(*
A few different attemps at making get_seq_no be further from the decompiled code
and more readable.

val get_seq_no_def = Define `get_seq_no (buf :otp_buffer) : num =
   w2n (((w2w ((buf 0) && 127w)) :word32 << 7) || w2w(((buf 1) && 127w)))
`;

val get_seq_no_def = Define `get_seq_no (buf :otp_buffer) : num =
  w2n (FCP_CONCAT ((word_bits 6 0 (buf 0)):word7) ((word_bits 6 0 (buf 1)) :word7))`;


val get_seq_no_def = Define `get_seq_no (buf :otp_buffer) :bool[14] = 
         bit_field_insert 6 0 (buf 1) (bit_field_insert 13 7 (buf 0) 0w)`

*)

val get_seq_no_def = Define `get_seq_no (buf :otp_buffer) :num = 
    let
      a = bit_field_insert 13 7 (buf 0) (0w:bool[14])
    in
      w2n (bit_field_insert 6 0 (buf 1) a)
    `

val test_buffer_def = Define `test_buffer = 
    ((0 =+ 255w) ((1 =+ 255w) buffer))`;


EVAL ``get_seq_no test_buffer``

val seq_in_order_def = Define `seq_in_order curr new =
                        (curr < new /\ curr < max_seq)`;

val encrypt_def = Define `encrypt v k = v ?? k`; 

val encrypt_buffer_def = Define `encrypt_buffer (f :otp_buffer) (key :otp_key_stream) (seq :num) =
                         ((2 =+ encrypt (f 2) (key (8*seq)))
                         ((3 =+ encrypt (f 3) (key (8*seq+1)))
                         ((4 =+ encrypt (f 4) (key (8*seq+2)))
                         ((5 =+ encrypt (f 5) (key (8*seq+3)))
                         ((6 =+ encrypt (f 6) (key (8*seq+4)))
                         ((7 =+ encrypt (f 7) (key (8*seq+5)))
                         ((8 =+ encrypt (f 8) (key (8*seq+6)))
			 ((9 =+ encrypt (f 9) (key (8*seq+7))) f))))))))`;


! seq1 seq2. seq1 != seq2 ==> g(seq1) not in g(seq2)

val zero_datah_def = Define `zero_datah (f : otp_buffer) = 
                         ((2 =+  ((f 2) && 127w))
                         ((3 =+  ((f 3) && 127w))
                         ((4 =+  ((f 4) && 127w))
                         ((5 =+  ((f 5) && 127w))
                         ((6 =+  ((f 6) && 127w))
                         ((7 =+  ((f 7) && 127w))
                         ((8 =+  ((f 8) && 127w))
                         ((9 =+  ((f 9) && 127w)) f))))))))`;

(*
val uart_write_def = Define `uart_write (out :otp_output_stream) (b :byte) =
                     APPEND out (b::[])`; *)

val uart_write_buffer_def = Define `uart_write_buffer (out :otp_output_stream) (buf :otp_buffer) =
                     APPEND out ((buf 0)::(buf 1)::(buf 2)::(buf 3)::(buf 4)::(buf 5)::(buf 6)::(buf 7)::(buf 8)::(buf 9)::[])`;

val tls_otp_spec_def = Define `tls_otp_spec (s : otp_state) :otp_state =
       s with Buffer :=  put_val_in_buf (shift_buffer s.Buffer) (uart_read s.In)`


val tls_otp_spec_def = Define `tls_otp_spec (s : otp_state) :otp_state =
    let 
       s' = s with <| Buffer := put_val_in_buf (shift_buffer s.Buffer) (uart_read s.In);
                      In := (TL s.In)|> in
    if(valid(s'.Buffer)) then
       let seq_no = get_seq_no s'.Buffer in
       if(seq_in_order s'.CurrSeq seq_no) then
          let
          newBuf = zero_datah (encrypt_buffer s'.Buffer s'.Key seq_no) in
          let newOut = uart_write_buffer s'.Out newBuf in
          s' with <|  Buffer := newBuf; CurrSeq := seq_no; Out := newOut |>
       else
          s'
    else
       s'
`;




val badInput = Define `badInput = 0w::0w::0w::0w::0w::0w::0w::0w::0w::0w::[] :otp_input_stream`;
val badOutput = Define `badOutput = [] :otp_output_stream`;
val badKey = Define `badKey :otp_key_stream = \i . ((n2w i) :byte)`;

val badState = Define `badState = <| Buffer := buffer; CurrSeq := 0;  In := badInput; Out := badOutput; Key := badKey|>`;

val badState2 = Define `badState2 = <| Buffer := buffer; CurrSeq := 0;  In := []; Out := badOutput; Key := badKey|>`;

val niceInput = Define `niceInput = 128w::129w::16w::16w::16w::16w::16w::16w::16w::16w::[] :otp_input_stream`;

val niceState = Define `niceState =  <| Buffer := buffer; CurrSeq := 0;  In := niceInput; Out := badOutput; Key := badKey|>`;


val test = EVAL ``badState2  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec ``;

val test = EVAL ``niceState  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec  :> tls_otp_spec ``;

(* dont run below on badState2... *)
val simp = SIMP_RULE arith_ss [UPDATE_def] test;

val simp2 = REWRITE_RULE [UPDATE_def] test;

val _ = export_theory();
