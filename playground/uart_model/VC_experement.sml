open m0u_progTheory;
open Int;
open m0_decompLib;
open m0Theory;
open progSyntax;
open pairLib;
open pred_setSyntax;
open m0_progLib;
open m0_stepLib;
open wordsSyntax;
 
thumb_decode_hex false "0000  "
 
register_instruction
 
val (code_th, code_defs) = m0_decompile "code"` 
  00c0
  1814
  5ce5
`;

val   code2_thm =  m0_spec_hex "f7ffffb9"
m0_spec_hex "00C0"
``0xffffw``

 open m0_progLib;
	  m0_get_code ``(p,INL 192w)``

get_code (m0_spec "BL")

m0_sp

(( fmt StringCvt.HEX o uint_of_word o snd o  dest_comb o  snd o  dest_pair o  hd o strip_set o  #3 o  dest_spec o concl) code_th) 
    
case (( dest_comb o  snd o  dest_pair o  hd o strip_set o  #3 o  dest_spec o concl) code_th) of
    ("INL", inst) => uint_of_word inst 
  | ("INR", inst) => uint_of_word inst;



dest_prod

dist_pair inst
