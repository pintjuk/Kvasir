open m0_progTheory

v=






spec |> #1|>concl 





``SPEC M0_MODEL (¬m0_NZCV * emp) 
      { (p + (4w :word32),(INL (30731w :word16) :word16 + word32)); (p + (2w :word32),(INL (30731w :word16) :word16 + word32));}
         (m0_REG RName_4 r4)``


val spec = m0_decompile_code "simpleOTP" `
(*movs r1, #0
movs r2, #100
ldrb r3, [r1, #0]
ldrb r4, [r2, #0]*)
eors r3, r4
strb r3, [r1]`;

``a=y``

ASSUME_TAC ``a<>e``
    
val spec = m0_decompile_code "simpleOTP" `
movs r1, #0
movs r2, #100
ldrb r3, [r1, #0]
ldrb r4, [r2, #0]
eors r3, r4
strb r3, [r1, #0]

ldrb r3, [r1, #1]
ldrb r4, [r2, #1]
eors r3, r4
strb r3, [r1, #1]

ldrb r3, [r1, #2]
ldrb r4, [r2, #2]
eors r3, r4
strb r3, [r1, #2]

ldrb r3, [r1, #3]
ldrb r4, [r2, #3]
eors r3, r4
strb r3, [r1, #3]

ldrb r3, [r1, #4]
ldrb r4, [r2, #4]
eors r3, r4
strb r3, [r1, #4]

ldrb r3, [r1, #5]
ldrb r4, [r2, #5]
eors r3, r4
strb r3, [r1, #5]


ldrb r3, [r1, #6]
ldrb r4, [r2, #6]
eors r3, r4
strb r3, [r1, #6]

ldrb r3, [r1, #7]
ldrb r4, [r2, #7]
eors r3, r4
strb r3, [r1, #7]


ldrb r3, [r1, #8]
ldrb r4, [r2, #8]
eors r3, r4
strb r3, [r1, #8]

ldrb r3, [r1, #9]
ldrb r4, [r2, #9]
eors r3, r4
strb r3, [r1, #9]
`;
DB.find "m0_MEMORY"


val (a,b) = spec |>(I ## (fn x =>  x|> SIMP_RULE (arith_ss++boolSimps.LET_ss ++WORD_ss++WORD_EXTRACT_ss)
                 [
                    GSYM CONJ_ASSOC,
                  combinTheory.UPDATE_APPLY
                  ]))

val test_thm =prove(``!x y dmem.(x<>y)/\(x IN dmem ==> x IN (dmem DELETE y))``, cheat)

val mem_trm = mk_var("mem", mk_int_word_type 32 --> mk_int_word_type 8)
val mem_split = prove( (*subst [``mem':word32->word8``|->mem_trm]*) ``!c.c IN dm ==> (m0_MEMORY dm (m:word32-> word8) = m0_MEM (c) (m c) * m0_MEMORY (dmem DELETE c) m)``, cheat) 

DB.find "HIDE_POST"
SPECL [``M0_MODEL``] progTheory.SPEC_HIDE_POST


val reg_hide =  prove(``!a.(m0_REG RName_3 (r3 ⊕ r4)) a ==> ( ~(m0_REG RName_3)) a``, cheat)
val c = a |> REWRITE_RULE [b]
  |> SIMP_RULE (std_ss++boolSimps.LET_ss ++boolSimps.CONJ_ss) [ SPEC_MOVE_COND]
  |> SIMP_RULE (bool_ss++pred_setLib.PRED_SET_ss) [test_thm, m0_MEMORY_INSERT |> GSYM |> GEN_ALL];
  (*does not work for some reason simplifier says "bad wars"*)
  |> SIMP_RULE (bool_ss) [mem_split]
  |> SIMP_RULE std_ss [GSYM STAR_ASSOC, SPEC_HIDE_POST]
     
     
(* would be nice to firther simplify things by expresing this as a function on SEP_ARRAYS *)
set_sepTheory.SEP_ARRAY_def












(* lets verify a spec *)
val encrypt  = Define `encrypt x y =  (x,y):> ZIP:> MAP (\a. FST a?? SND a)`


``!p c base_msg base_key m.  SPEC M0_MODEL
(~m0_NZCV * m0_COUNT c * m0_PC p * m0_REG RName_1 base_msg * m0_REG RName_2 base_key * ¬m0_REG RName_3 * ¬m0_REG RName_4 * ~m0_MEM base_key * ~m0_MEM base_msg)
       {(p,INL 30731w); 
        (p + 2w,INL 30740w);
        (p + 4w,INL 16483w);
        (p + 6w,INL 28683w)} 
(¬m0_NZCV * m0_COUNT (c + 7) * m0_PC (p + 8w) *  (m0_MEM base_msg (m base_msg  ⊕ m base_key)) * ~m0_MEM base_key *
 m0_REG RName_1 base_msg * m0_REG RName_2 base_key * ¬m0_REG RName_3 * ¬m0_REG RName_4 

) 


(* spec of encrypt code *)

``!p c base_msg base_key m.  SPEC M0_MODEL
(~m0_NZCV * m0_COUNT c * m0_PC p * SEP_ARRAY m0_MEM 1w base_msg msg
* SEP_ARRAY m0_MEM 1w base_key key * m0_REG RName_2 base_key * ¬m0_REG RName_3 * ¬m0_REG RName_4)
      OTP_CODE
      (¬m0_NZCV * m0_COUNT (c + 7) * m0_PC (p + 8w) *  
       SEP_ARRAY m0_MEM 1w base_key key *
       SEP_ARRAY m0_MEM 1w base_msg (encrypt msg key) *
       m0_REG RName_1 base_msg * m0_REG RName_2 base_key * ¬m0_REG RName_3 * ¬m0_REG RName_4
) 
``


DB.find "SEP_ARRAY"
``l = SEP_ARRAY m0_MEM 4w 1000w [1w, 2w, 3w]``

 [1w,2w]``
``l=(m0_MEMORY dm)``

       (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dm m *
        m0_REG RName_1 r1 * m0_REG RName_2 r2 * ¬m0_REG RName_3 *
        ¬m0_REG RName_4)
       (¬m0_NZCV * m0_COUNT (count + 7) * m0_PC (p + 8w) *
        (m0_MEM r1 (m r1 ⊕ m r2) * m0_MEMORY (dm DELETE r1) m) *
        m0_REG RName_1 r1 * m0_REG RName_2 r2 *
        m0_REG RName_3 ((7 >< 0) (m r1) ⊕ (7 >< 0) (m r2)) *
        m0_REG RName_4 ((7 >< 0) (m r2)))``
 









val test_thm= prove(``
 !a b c x y f. a <> b ==> ( (b=+y)((a=+x)f) =((c =+ y) o (a =+ x)) f  )
``,cheat)




spec |>(I ## (fn x =>  x|> SIMP_RULE (arith_ss++boolSimps.LET_ss ++WORD_ss++WORD_EXTRACT_ss)
                 [
 (*                 BBLAST_CONV ``!r1.r1:word32 <> r1+1w``,
                  BBLAST_CONV ``!r1.(r1:word32)+1w <> r1+2w``,*)
                  combinTheory.UPDATE_APPLY]))


`` ((1w =+ mem 1w ?? mem 101w)       ((0w =+ mem 0w ?? mem 100w) mem)``


open wordsLib
``(x:word32) ?? (x:word32)``



          


open blastLib
  bool_simsLib.LET_ss
val (m0_encrypt_th, m0_encrypt_defs) = m0_decompile "m0_encrypt"`
 00c0   (* lsls	r0, r0, #3	*)
 
 5c14   (* ldrb	r4, [r2, r0]	*)
 788b   (* ldrb	r3, [r1, #2]	*)
 1812   (* adds	r2, r2, r0	*)
 4063   (* eors	r3, r4		*)
 708b   (* strb	r3, [r1, #2]	*)
 
 7850   (* ldrb	r0, [r2, #1]	*)
 78cb   (* ldrb	r3, [r1, #3]	*)
 4043   (* eors	r3, r0		*)
 70cb   (* strb	r3, [r1, #3]	*)

 7890   (* ldrb	r0, [r2, #2]	*)
 790b   (* ldrb	r3, [r1, #4]	*)
 4043   (* eors	r3, r0		*)
 710b   (* strb	r3, [r1, #4]	*)

 78d0   (* ldrb	r0, [r2, #3]	*)
 794b   (* ldrb	r3, [r1, #5]	*)
 4043   (* eors	r3, r0		*)
 714b   (* strb	r3, [r1, #5]	*)

 7910   (* ldrb	r0, [r2, #4]	*)
 798b   (* ldrb	r3, [r1, #6]	*)
 4043   (* eors	r3, r0		*)
 718b   (* strb	r3, [r1, #6]	*)
 
 7950   (* ldrb	r0, [r2, #5]	*)
 79cb   (* ldrb	r3, [r1, #7]	*)
 4043   (* eors	r3, r0		*)
 71cb   (* strb	r3, [r1, #7]	*)
 
 7990   (* ldrb	r0, [r2, #6]	*)
 7a0b   (* ldrb	r3, [r1, #8]	*)
 4043   (* eors	r3, r0		*)
 720b   (* strb	r3, [r1, #8]	*)
 79d2   (* ldrb	r2, [r2, #7]	*)
 7a4b   (* ldrb	r3, [r1, #9]	*)
 4053   (* eors	r3, r2		*)
 724b   (* strb	r3, [r1, #9]	*)
`;


 
