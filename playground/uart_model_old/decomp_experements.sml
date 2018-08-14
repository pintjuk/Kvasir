        
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/model"::(!loadPath));
loadPath := ("/Home/daniil/HOL/examples/l3-machine-code/common"::(!loadPath));
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));
open  wordsTheory;
open m0Theory;
open m0_decompLib;
open fcpTheory;

val (code_th, code_defs) = m0_decompile "code"` 
  00c0
  1814
  5ce5
`;


val (ldrb_th, ldrb_defs) = m0_decompile "ldrb"` 
  5ce5
`;

val restrict_ldrb_th = prove(``! count dmem mem r3 r4 .
SPEC M0_MODEL
    (m0_COUNT count * m0_PC 300w * m0_MEMORY dmem mem * m0_REG RName_3 r3 *
     m0_REG RName_4 r4 * ¬m0_REG RName_5 *
     cond (ldrb_pre (r3,r4,count,dmem,mem) /\ r3 + r4 < 200000w) ) {(300w,INL 23781w)}
    (let
       (r3,r4,r5,count,dmem,mem) = ldrb (r3,r4,count,dmem,mem)
     in
       m0_COUNT count * m0_PC (300w + 2w) * m0_MEMORY dmem mem *
       m0_REG RName_3 r3 * m0_REG RName_4 r4 * m0_REG RName_5 r5)
``,			    
let 
 val X = DB.find "SPEC_MOVE_COND" |> List.hd|>snd|>fst 
 val L =  Ho_Rewrite.ONCE_REWRITE_RULE [X] ldrb_th  |> GEN_ALL
in 
 Ho_Rewrite.REWRITE_TAC [X]>>
 SIMP_TAC std_ss [L]
end);

decompilerLib.add_decompiled ("LDRB", SPEC_ALL restrict_ldrb_th 
, 2, SOME 2);

val (code_th, code_defs) = m0_decompile "code"` 
00c0
1814
insert: LDRB
`

DB.find "SEP_IMP_REFL"

``SEP_IMP (m0_COUNT count * m0_PC p * m0_MEMORY dmem mem * m0_REG RName_3 r3 *
     m0_REG RName_4 r4 * ¬m0_REG RName_5 *
     cond (ldrb_pre (r3,r4,count,dmem,mem)))

     (m0_COUNT count * m0_PC p * m0_MEMORY dmem mem * m0_REG RName_3 r3 *
     m0_REG RName_4 r4 * ¬m0_REG RName_5 *
     cond (ldrb_pre (r3,r4,count,dmem,mem)))``
EVAL_RULE code_defs
EVAL_RULE ldrb_defs



val (test2_cert, test2_def) = m0_decompile_code "test2" `
	mov	r3, #0  		
	lsls	r0, r0, #3 
L:	adds	r4, r2, r0 		; r4 = key+ seq_no << 3
	ldrb	r5, [r4, r3] 		; r5 = *(key+seq_no<<3+r3)
	ldrb	r4, [r1, r3] 		; r4 = *(buffer+r3)
	eors	r4, r5 			; r4 ^= r5 
	strb	r4, [r1, r3] 		; *(buffer+r3)= r4
	adds	r3, r3, #1 		; r3+=1
cmp	r3, #8                  ;
bne	L                    ; goto l10 if (r3 != 8)
`
val 

val (test2_cert, test2_def) = m0_decompile "test2" `
2300  
00c0 
1814
5ce5  
5ccc 
406c 
54cc
3301 
2b08 
d1f7`



val (test2_cert, test2_def) = m0_decompile "test2" `
d1f7`
DB.match []  ``d1f7``



val (test2_cert, test2_def) = m0_decompile_code "test2" `
cmp	r3, #8                  ;
bne	L                    ; goto l10 if (r3 != 8)
`






val n = prove(``!r0 r1 r2 r3 count dmem mem.
  (test21 (r0,r1,r2,r3,count,dmem,mem) =
   if r3 + 1w = 8w then
     (r0,r1,r2,r3 + 1w,w2w (mem (r1 + r3)) ⊕ w2w (mem (r2 + r0 + r3)),
      w2w (mem (r2 + r0 + r3)),count + 1 + 2 + 2 + 1 + 2 + 1 + 1 + 1,
      dmem,
      (r1 + r3 =+
       (7 >< 0) (w2w (mem (r1 + r3)) ⊕ w2w (mem (r2 + r0 + r3)))) mem)
   else
     test21
       (r0,r1,r2,r3 + 1w,count + 1 + 2 + 2 + 1 + 2 + 1 + 1 + 3,dmem,
        (r1 + r3 =+
         (7 >< 0) (w2w (mem (r1 + r3)) ⊕ w2w (mem (r2 + r0 + r3))))
          mem))``,
	  
SIMP_TAC arithm_ss []
EVAL_TAC

)


``!r0 r1 r2 r3 count dmem mem.
  (test21 (r0,r1,r2,r3,count,dmem,mem) =
  (r0, r1, r2, 8w,
   w2w (mem (r1 + 8w)) ⊕ w2w (mem (r2 + r0 + 8w)),
   w2w (mem (r2 + r0 + 8w)),
  count+11* w2n(8w-r3),
  dmem,
  \a.  if r1 +r3 <= a /\ a <= r1+8w
       then (7 >< 0) (w2w (mem a) ⊕ w2w (mem (r2 + r0 + (a-r1))))
       else mem a))
       
``
REPEAT STRIP_TAC
Induct_on `w2n (8w - r3)`

`r3 = 7w` by 
DB.match
DB.match [] ``_/\ (∀n. P _ ⇒ P _) ⇒ ∀n. P _``
DB.find  "induct"
EVAL_TAC

ONCE_REWRITE_TAC [test2_def]
EVAL_TAC


DB.find "while"
EVAL_TAC

