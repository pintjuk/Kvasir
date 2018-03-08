open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open BasicProvers
open markerLib
open wordsLib;

val _ = new_theory "otpModel";

val _ = type_abbrev("byte", ``:bool[8]``);
val _ = type_abbrev("otp_input_stream", ``:num -> byte``);
val _ = type_abbrev("otp_key_stream", ``:num -> byte``);
val _ = type_abbrev("otp_output_stream", ``:num -> byte``);

val otp_phi_start_del = Define `
otp_phi_start (I:otp_input_stream) (k:num) =
 (word_msb (I k)) /\ (word_msb (I (k + 1))) /\
 (~(word_msb (I (k + 2)))) /\ (~(word_msb (I (k + 3)))) /\
 (~(word_msb (I (k + 4)))) /\ (~(word_msb (I (k + 5)))) /\
 (~(word_msb (I (k + 6)))) /\ (~(word_msb (I (k + 7)))) /\
 (~(word_msb (I (k + 8)))) /\ (~(word_msb (I (k + 9))))
`;



val example_input_def = Define `
example_input x =
  if (x =0) then 128w:byte else
  if (x =1) then 128w else
  if (x =2) then 0w else
  if (x =3) then 0w else
  if (x =4) then 0w else
  if (x =5) then 0w else
  if (x =6) then 0w else
  if (x =7) then 0w else
  if (x =8) then 0w else
  if (x =9) then 0w else
  if (x =10) then 0w else
  if (x =11) then 0w else
  if (x =12) then 128w else
  if (x =13) then 128w else
  if (x =14) then 0w else
  if (x =15) then 0w else
  0w
`;

val thm1 = EVAL ``MAP (otp_phi_start example_input)
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]``

(* TO PROVE *)
``!x y I . (x - y < 10) ==>
         (x < y)
         (otp_phi_start I x) ==>
         (~(otp_phi_start I y))
``;

val otp_phi_msg_del = Define `
otp_phi_msg (I:otp_input_stream) k =
 (?k'. (k-9 <= k') /\ (k' <= k) /\ (otp_phi_start I k'))
`;

val thm1 = prove(``otp_phi_msg example_input 0``,
  EVAL_TAC >>
  EXISTS_TAC ``0:num`` >>
  EVAL_TAC
);
val thm1 = prove(``otp_phi_msg example_input 1``,
  EVAL_TAC >>
  EXISTS_TAC ``0:num`` >>
  EVAL_TAC
);
val thm1 = prove(``~(otp_phi_msg example_input 10)``,
  EVAL_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  GEN_TAC >>
  Cases_on `k' < 1` >>
    (FULL_SIMP_TAC arith_ss [] )
);

val otp_phi_msg_def = Define `
otp_phi_msg (I:otp_input_stream) k =
  let starts = otp_phi_start I in
  (?k'. (k-9 <= k') /\ (k' <= k) /\ (starts k'))
`;

val thm1 = EVAL ``MAP (otp_phi_msg example_input)
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]``

val thm1 = prove( ``(MAP (otp_phi_msg example_input)
[0; 1; 2; 3]) =
[T; T; T; T]
``,


   SIMP_TAC (list_ss++ARITH_ss++WORD_ss) [ otp_phi_msg_def, example_input_def, otp_phi_start_del]>>
 LET_ELIM_TAC>>
 UNABBREV_ALL_TAC>>(
   TRY (EXISTS_TAC ``0``) >>
   SIMP_TAC (std_ss++WORD_ss) [ otp_phi_msg_def, example_input_def, otp_phi_start_del]
 )
)

DB.find  "Abbrev"

val thm1 = EVAL ``otp_phi_start example_input 0``;
val thm1 = EVAL ``otp_phi_start example_input 10``;
val thm1 = EVAL ``otp_phi_start example_input 12``;
val thm1 = EVAL ``otp_phi_start example_input 13``;
val thm1 = EVAL ``otp_phi_start example_input 14``;
val thm1 = EVAL ``otp_phi_start example_input 17``;
val thm1 = EVAL ``otp_phi_start example_input 17``;

(*** list model ***)

val _ = type_abbrev("byte", ``:bool[8]``);
val _ = type_abbrev("otp_input_stream", ``: byte list``);
val _ = type_abbrev("otp_key_stream", ``:byte list``);
val _ = type_abbrev("otp_output_stream", ``:byte list``);

val example_input_def = Define `
example_input = 0w::128w:byte::255w::0w::0w::0w::0w::0w::0w::0w::0w::0w::[]
`;


val otp_phi_start_def = Define `
(otp_phi_start ((b0::b1::b2::b3::b4::b5::b6::b7::b8::b9::others): otp_input_stream) =
 ((word_msb b0) /\ (word_msb b1) /\
 (~(word_msb b2)) /\ (~(word_msb b3)) /\ (~(word_msb b4)) /\ (~(word_msb b5)) /\
 (~(word_msb b6)) /\ (~(word_msb b7)) /\ (~(word_msb b8)) /\ (~(word_msb b9))
 ) :: (otp_phi_start (b1::b2::b3::b4::b5::b6::b7::b8::b9::others))
)  /\
(otp_phi_start others = MAP (\x.F) others)
`;

val thm1 = EVAL ``otp_phi_start example_input``;




val _ = export_theory();