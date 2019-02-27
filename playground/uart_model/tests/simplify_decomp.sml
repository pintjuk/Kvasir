(*
    loadPath := ("/home/daniil/Apps/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));
    loadPath := ("/home/daniil/Apps/HOL/examples/l3-machine-code/m0/prog"::(!loadPath));
    loadPath := ("/Home/daniil/Apps/HOL/examples/l3-machine-code/common"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/helpers"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/nit2bisim"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/prog"::(!loadPath));
*)
open m0_progTheory
open wordsLib
open m0_decompLib



fun simplifySpec sp=  sp |>(I ## (fn x =>  x|> SIMP_RULE (arith_ss++ boolSimps.CONJ_ss++boolSimps.LET_ss ++WORD_ss++WORD_EXTRACT_ss)
                 [
                    GSYM CONJ_ASSOC,
                  combinTheory.UPDATE_APPLY
                  ]))
                        
                        
val spec =  
`(*movs r1, #0
movs r2, #100*)
movs r3, #4
label:
ldrb r4, [r1, r3]
ldrb r5, [r2, r3]
eors r4, r5
strb r4, [r6, r3]
subs r3, r3, #1
bne label
`
 |> (m0_decompile_code "simpleOTP")
 |> simplifySpec
;


val spec =`
movs r1, #100
ldrb r2, [r3, #0]
strb r2, [r6, #0]
ldrb r2, [r3, #1]
strb r2, [r6, #1]
ldrb r2, [r3, #2]
strb r2, [r6, #2]
`|> (m0_decompile_code "simpleOTP")
 |> simplifySpec
;

val spec =`
movs r2, #100
strb r2, [r1, #0]
strb r2, [r1, #1]
strb r2, [r1, #2]
strb r2, [r1, #3]
strb r2, [r1, #4]
strb r2, [r1, #5]
`|> (m0_decompile_code "simpleOTP")
 |> simplifySpec
;

val spec = `
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
`|> (m0_decompile_code "simpleOTP")
 |> simplifySpec
;
DB.find "m0_MEMORY"





val test_thm =prove(``!x y dmem.(x<>y)/\(x IN dmem ==> x IN (dmem DELETE y))``, cheat)

val mem_trm = mk_var("mem", mk_int_word_type 32 --> mk_int_word_type 8)
val mem_split = prove( (*subst [``mem':word32->word8``|->mem_trm]*) ``!c.c IN dm ==> (m0_MEMORY dm (m:word32-> word8) = m0_MEM (c) (m c) * m0_MEMORY (dmem DELETE c) m)``, cheat) 

val c = a |> REWRITE_RULE [b]
  |> SIMP_RULE (std_ss++boolSimps.LET_ss ++boolSimps.CONJ_ss) [SPEC_MOVE_COND]
  |> SIMP_RULE (bool_ss++pred_setLib.PRED_SET_ss) [test_thm, m0_MEMORY_INSERT |> GSYM |> GEN_ALL];

set_trace "simplifier" 2

  c |> SIMP_RULE (bool_ss++pred_setLib.PRED_SET_ss) [test_thm, m0_MEMORY_INSERT |> GSYM |> GEN_ALL];
  c |> SIMP_RULE (bool_ss) [mem_split]
    |> SIMP_RULE (arith_ss++boolSimps.LET_ss ++WORD_ss++WORD_EXTRACT_ss)
                 [
                    GSYM CONJ_ASSOC,
                  combinTheory.UPDATE_APPLY
                  ]
  |> SIMP_RULE (std_ss) [GSYM set_sepTheory.SEP_ARRAY_def, ]


  


(* would be nice to firther simplify things by expresing this as a function on SEP_ARRAYS *)
set_sepTheory.SEP_ARRAY_def




val test_thm= prove(``
 !a b c x y f. a <> b ==> ( (b=+y)((a=+x)f) =((c =+ y) o (a =+ x)) f  )
``,cheat)




spec |>(I ## (fn x =>  x|> SIMP_RULE (arith_ss++boolSimps.LET_ss ++WORD_ss++WORD_EXTRACT_ss)
                 [
 (*                 BBLAST_CONV ``!r1.r1:word32 <> r1+1w``,
                  BBLAST_CONV ``!r1.(r1:word32)+1w <> r1+2w``,*)
                  combinTheory.UPDATE_APPLY]))


`` ((1w =+ mem 1w ?? mem 101w)       ((0w =+ mem 0w ?? mem 100w) mem)``


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


 
