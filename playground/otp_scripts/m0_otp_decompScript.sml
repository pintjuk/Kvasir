
open HolKernel boolLib bossLib Parse;


(*
Run these if you are using interactive mode.

loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0/decompiler")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/common")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/hoare-triple")::(!loadPath));
*)

open progTheory;
open m0_decompLib;
open helperLib;


val _ = new_theory "m0_otp_decomp";


val (m0_shift_buffer_th, m0_shift_buffer_defs) = m0_decompile "m0_shift_buffer"`
 7843      (* ldrb	r3, [r0, #1] *)
 7003      (* strb	r3, [r0, #0] *)
 7883      (* ldrb	r3, [r0, #2] *)
 7043      (* strb	r3, [r0, #1] *)
 78c3      (* ldrb	r3, [r0, #3] *)
 7083      (* strb	r3, [r0, #2] *)
 7903      (* ldrb	r3, [r0, #4] *)
 70c3      (* strb	r3, [r0, #3] *)
 7943      (* ldrb	r3, [r0, #5] *)
 7103      (* strb	r3, [r0, #4] *)
 7983      (* ldrb	r3, [r0, #6] *)
 7143      (* strb	r3, [r0, #5] *)
 79c3      (* ldrb	r3, [r0, #7] *)
 7183      (* strb	r3, [r0, #6] *)
 7a03      (* ldrb	r3, [r0, #8] *)
 71c3      (* strb	r3, [r0, #7] *)
 7a43      (* ldrb	r3, [r0, #9] *)
 7203      (* strb	r3, [r0, #8] *)
 2300      (* movs	r3, #0       *)
 7243      (* strb	r3, [r0, #9] *) 
`;


val th = Theory.save_thm("m0_hoare_shift", m0_shift_buffer_th);


val (m0_validate_datah_th, m0_validate_datah_defs) = m0_decompile "m0_validate_datah"`
  78c3    (* ldrb	r3, [r0, #3] *)
  7882    (* ldrb	r2, [r0, #2] *)
  431a    (* orrs	r2, r3	     *)
  7903    (* ldrb	r3, [r0, #4] *)
  431a    (* orrs	r2, r3	     *)
  7943    (* ldrb	r3, [r0, #5] *)
  431a    (* orrs	r2, r3	     *)
  7983    (* ldrb	r3, [r0, #6] *)
  431a    (* orrs	r2, r3	     *)
  79c3    (* ldrb	r3, [r0, #7] *)
  431a    (* orrs	r2, r3	     *)
  7a03    (* ldrb	r3, [r0, #8] *)
  431a    (* orrs	r2, r3	     *)
  7a43    (* ldrb	r3, [r0, #9] *)
  431a    (* orrs	r2, r3       *)
  43d0    (* mvns	r0, r2 	     *)
  09d0    (* lsrs	r0, r2, #7   *)
  43c0    (* mvns	r0, r0       *)
`; 

val th = Theory.save_thm("m0_hoare_datah", m0_validate_datah_th);

val (m0_validate_seqh_th, m0_validate_seqh_defs) = m0_decompile "m0_validate_seqh" `
 7803    (*	ldrb	r3, [r0, #0] *)
 7840    (*	ldrb	r0, [r0, #1] *)
 4018    (*	ands	r0, r3 		 *)
 09c0    (*	lsrs	r0, r0, #7 *)
`;

val th = Theory.save_thm("m0_hoare_seqh", m0_validate_seqh_th);

val (m0_get_seq_no_th, m0_get_seq_no_defs) = m0_decompile "m0_get_seq_no" `
 22fe   (* movs	r2, #254	; 0xfe  *)
 7803   (* ldrb	r3, [r0, #0]		*)
 0192   (* lsls	r2, r2, #6		*)
 01db   (* lsls	r3, r3, #7		*)
 4013   (* ands	r3, r2			*)
 227f   (* movs	r2, #127	; 0x7f	*)
 7840   (* ldrb	r0, [r0, #1]		*)
 4010   (* ands	r0, r2			*)
 18c0   (* adds	r0, r0, r3		*)
`;

val th = Theory.save_thm("m0_hoare_get_seq", m0_get_seq_no_th);

val (m0_encrypt_th, m0_encrypt_defs) = m0_decompile "m0_encrypt"`
 b510   (* push	{r4, lr}	*)
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


val th = Theory.save_thm("m0_hoare_encrypt", m0_encrypt_th);

val (m0_zero_headers_th, m0_zero_headers_defs) = m0_decompile "m0_zero_headers"`
  237f   (*	movs	r3, #127	; 0x7f	*)
  7882   (*	ldrb	r2, [r0, #2]		*)
  401a   (*	ands	r2, r3			*)
  7082   (*	strb	r2, [r0, #2]		*)
  78c2   (*	ldrb	r2, [r0, #3]		*)
  401a   (*	ands	r2, r3			*)
  70c2   (*	strb	r2, [r0, #3]		*)
  7902   (*	ldrb	r2, [r0, #4]		*)
  401a   (*	ands	r2, r3			*)
  7102   (*	strb	r2, [r0, #4]		*)
  7942   (*	ldrb	r2, [r0, #5]		*)
  401a   (*	ands	r2, r3			*)
  7142   (*	strb	r2, [r0, #5]		*)
  7982   (*	ldrb	r2, [r0, #6]		*)
  401a   (*	ands	r2, r3			*)
  7182   (*	strb	r2, [r0, #6]		*)
  79c2   (*	ldrb	r2, [r0, #7]		*)
  401a   (*	ands	r2, r3			*)
  71c2   (*	strb	r2, [r0, #7]		*)
  7a02   (*	ldrb	r2, [r0, #8]		*)
  401a   (*	ands	r2, r3			*)
  7202   (*	strb	r2, [r0, #8]		*)
  7a42   (*	ldrb	r2, [r0, #9]		*)
  4013   (*	ands	r3, r2			*)
  7243   (*	strb	r3, [r0, #9]		*)
`;

val th = Theory.save_thm("m0_hoare_zeroh", m0_zero_headers_th);

(*
val (driver_uart_write_th, driver_uart_write_defs) = m0_decompile "driver_uart_write"`

`;

val (driver_uart_read_th, driver_uart_read_defs) = m0_decompile "driver_uart_read"`

`;
*)

val (m0_valid_msg_th, m0_valid_msg_defs) = m0_decompile "m0_valid_msg" ` 
 b5f8        (*	push	{r3, r4, r5, r6, r7, lr} *)
 0007       (*	movs	r7, r0 *)
 000c       (*	movs	r4, r1 *)
 0016       (*	movs	r6, r2 *)

` 

 insert: m0_validate_seqh
 (*  f7ff ffe2 *) (*	bl	162 <validate_seq_headers> *)
 0005       (*	movs	r5, r0 *)
 0038       (*	movs	r0, r7 *)
 insert: m0_validate_datah
 (*f7ff ffe3 *)  (*	bl	16c <validate_data_headers> *)
 2300       (*	movs	r3, #0 *)
 42a6       (*	cmp	r6, r4 *)
 da04       (*	bge.n	1b6 <valid_msg+0x24> *)
 4a07       (*	ldr	r2, [pc, #28]	; (1cc <valid_msg+0x3a>) *)
 0fe1       (*	lsrs	r1, r4, #31 *)
 42a2       (*	cmp	r2, r4 *)
 414b       (*	adcs	r3, r1 *)
 b2db       (*	uxtb	r3, r3 *)
 2d00       (*	cmp	r5, #0 *)
 d005       (*	beq.n	1c6 <valid_msg+0x34> *)
 2800       (*	cmp	r0, #0 *)
 d002       (*	beq.n	1c4 <valid_msg+0x32> *)
 0018       (*	movs	r0, r3 *)
 1e43       (*	subs	r3, r0, #1 *)
 4198       (*	sbcs	r0, r3 *)
 (* bdf8 *)       (*	pop	{r3, r4, r5, r6, r7, pc} *)
 0028       (*	movs	r0, r5 *)
 e7fc       (*	b.n	1c4 <valid_msg+0x32> *)
 46c0       (*	nop			; (mov r8, r8) *)
 (* 0001fff7 *)	(* .word	0x0001fff7 *)
`;


val (otp_process_messages_th, otp_process_messages_defs) = m0_decompile "m0_process_messages"`
 (*b5f0 *)      (* 	push	{r4, r5, r6, r7, lr} *)
 2700      (* 	movs	r7, #0 *)
 b087      (* 	sub	sp, #28 *)
 9001      (* 	str	r0, [sp, #4] *)
 (* f7ff ff56 *) (* 	bl	11c <uart_read> *)
 0005      (* 	movs	r5, r0 *)
 ac03      (* 	add	r4, sp, #12 *)
 0020      (* 	movs	r0, r4 *)
 insert: m0_shift_buffer
 (* f7ff ff5f *) (* 	bl	138 <shift_buffer> *)
 0020      (* 	movs	r0, r4 *)
 7265      (* 	strb	r5, [r4, #9] *)
 insert: m0_validate_seqh
 (*f7ff ff70*) (* 	bl	162 <validate_seq_headers> *)
 0006      (* 	movs	r6, r0 *)
 0020      (* 	movs	r0, r4 *)
 insert: m0_validate_datah
 (*f7ff ff71 *) (* 	bl	16c <validate_data_headers> *)
 9000      (* 	str	r0, [sp, #0] *)
 0020      (* 	movs	r0, r4 *)
 insert: m0_get_seq_no
 (*f7ff ff80 *) (* 	bl	192 <get_seq_no> *)
 0005      (* 	movs	r5, r0 *)
 42b8      (* 	cmp	r0, r7 *)
 dd02      (* 	ble.n	29e <process_messages+0x3a> *)
 4b0c      (* 	ldr	r3, [pc, #48]	; (2cc <process_messages+0x68>) *)
 4298      (* 	cmp	r0, r3 *)
 dd01      (* 	ble.n	2a2 <process_messages+0x3e> *)
 003d      (* 	movs	r5, r7 *)
 e010      (* 	b.n	2c4 <process_messages+0x60> *)
 9b00      (* 	ldr	r3, [sp, #0] *)
 431e      (* 	orrs	r6, r3 *)
 d0fa      (* 	beq.n	29e <process_messages+0x3a> *)
 9a01      (* 	ldr	r2, [sp, #4] *)
 0021      (* 	movs	r1, r4 *)
 0028      (* 	movs	r0, r5 *)
 insert: m0_encrypt
 (*f7ff ff7a *) (* 	bl	1a6 <encrypt> *)
 0020      (* 	movs	r0, r4 *)
 insert: m0_zero_headers
 (*f7ff ff9b *) (* 	bl	1ee <zero_data_headers> *)
 0020      (* 	movs	r0, r4 *)
 (*f7ff ffb2 *) (* 	bl	222 <write_to_uart> *)
 4b03      (* 	ldr	r3, [pc, #12]	; (2cc <process_messages+0x68>) *)
 429d      (* 	cmp	r5, r3 *)
 d001      (* 	beq.n	2c8 <process_messages+0x64> *)
 002f      (* 	movs	r7, r5 *)
 e7d1      (* 	b.n	26c <process_messages+0x8> *)
 b007      (* 	add	sp, #28 *)
`; 

(*
val (otp_process_messages1_th, otp_process_messages1_defs) = m0_decompile "m0_process_messages1"`
 (* b5f0 *)      (* 	push	{r4, r5, r6, r7, lr} *)
 2700      (* 	movs	r7, #0 *)
 b087      (* 	sub	sp, #28 *)
 9001      (* 	str	r0, [sp, #4] *)`;


val (test1_th, test1_defs) = m0_decompile "test_1"`
2700
`;

val (test2_th, test2_defs) = m0_decompile "test_2"`
b087
`;

val (testcom_th, testcom_defs) = m0_decompile "test_com"`
2700
b087
`;

val (testcom1_th, testcom1_defs) = m0_decompile "test_com1"`
insert: test_1
insert: test_2
`;

core_decompilerLib.compose test1_th test2_th;


decompilerLib.get_decompiled "test_com";
decompilerLib.add_decompiled ("roberto", test1_th, 2, SOME 2);
val (testcom1_th, testcom1_defs) = m0_decompile "test_com1"`
insert: roberto
insert: test_2
`;

type_of ``test_com``;

 val test1_simp = SIMP_RULE (arith_ss ++ wordsLib.WORD_ss) [LET_DEF, test1_defs] test1_th;

 val test2_simp = SIMP_RULE (arith_ss ++ wordsLib.WORD_ss) [LET_DEF, test2_defs] test2_th;

val thm_spec = SPECL [``r13:word32``, ``p+2w:word32``] (GEN_ALL test2_th);
val thm_spec1 = SPEC_ALL thm_spec;

val tst1tst2 = SPEC_COMPOSE_RULE [test1_th, thm_spec1]

type_of ``m0_COUNT``;
 val test2_simp = SIMP_RULE (arith_ss ++ wordsLib.WORD_ss) [LET_DEF, test2_defs] test2_th;

val otp_pc_specced_msgs1_th = SPEC ``0x1AAw :word32`` (GEN ``p :word32`` otp_process_messages1_th)

val thm1a = SIMP_RULE (arith_ss ++ wordsLib.WORD_ss) [LET_DEF, otp_process_messages1_defs] otp_pc_specced_msgs1_th


open core_decompilerLib

compose

core_decompilerLib
val th2a = replace_new_vars ("s" ^ int_to_string (varname_next ())) mupp4
val tst2 = SPEC_COMPOSE_RULE [thm1a, mupp4]


open helperLib
list_dest dest_sep_disj q
val th1 = th2
val th2 = mupp5
     val (_,_,_,q) = dest_spec (concl th1)
     val (_,p,_,_) = dest_spec (concl th2)
     val vs = list_dest dest_sep_exists q
     val (vs,q) = (butlast vs,last vs)
     val (xs1,xs2,ys1,ys2) = helperLib.match_and_partition (list_dest dest_star q) (list_dest dest_star p)
     val ty = type_of q
     val (m,i) = match_term (list_mk_star ys1 ty) (list_mk_star xs1 ty)
     val th2 = INST m (INST_TYPE i th2)

type_of dest_comb (concl thm1a)
val (a, b) = dest_comb (concl thm1a)
val (c, d) = dest_comb b
val (e, f) = dest_comb c

val (g, h) = dest_comb f

val xr = dest_sep_disj g
val xl = dest_star g
type_of g

*)
open m0;

open bitTheory;

open BitsN;

val IS_FIRST_BL_def = Define `isFirstBl (x:word16) = ((x && 0xF800w) = 0xF000w)`

val IS_SECOND_BL_def = Define `isSecondBl (y: word16) = ((y && 0xF800w) = 0xF800w)`

val BL_OFFSET_def = Define `(bl_offset (x :word16) (y :word16)) : word32 = w2w (((w2w (x && 2047w)) :word32 << 12) + ( (w2w (y && 2047w)) :word32 << 1) + 4w)`


val m0_bl_pre_def = Define `m0_bl_pre (r14, count, dmem, m) = T`


(* sanity check, for offset 0 *)
(*
prove(``bl_offset 63488w 61440w = 0w``,
  SIMP_TAC (arith_ss ++ wordsLib.WORD_ss) [BL_OFFSET_def]
); *)

open m0_core_decompTheory;
open m0_progTheory;
open sumTheory;
open decompilerLib;

val BL_HOARE_THM = prove(``
   !x y.
   isFirstBl(x) /\ isSecondBl(y) ==>
   (SPEC M0_MODEL (
     ((~m0_NZCV) * (m0_COUNT (count :num)) * (m0_PC (p :word32)) * 
      (m0_MEMORY dmem m) * (m0_REG RName_LR r14) *
      (cond (m0_bl_pre (r14, count, dmem, m)) : (m0_component # m0_data -> bool) -> bool)))
     {(p, INL x); ((p+(2w :word32)), INL y)}
     ((~m0_NZCV) * (m0_COUNT (count + 2)) * (m0_PC (p+4w)) * (m0_MEMORY dmem m) * 
      (m0_REG RName_LR (p + (bl_offset x y)))
   ))
``,
cheat
);


val BL_HOARE_THM = prove(``
   !x y.
    let m0_bl_pre in
    (SPEC M0_MODEL (
     ((~m0_NZCV) * (m0_COUNT (count :num)) * (m0_PC (p :word32)) * 
      (m0_MEMORY dmem m) * (m0_REG RName_LR r14) *
      (cond (m0_bl_pre (r14, count, dmem, m)) : (m0_component # m0_data -> bool) -> bool)))
     {(p, INL x); ((p+(2w :word32)), INL y)}
     ((~m0_NZCV) * (m0_COUNT (count + 2)) * (m0_PC (p+4w)) * (m0_MEMORY dmem m) * 
      (m0_REG RName_LR (p + (bl_offset x y)))
   ))
``,
cheat
);

val mupp = SPEC ``0xFFE2w :word16`` (SPEC ``0xF7FFw :word16`` BL_HOARE_THM);

val mupp2 = SIMP_RULE (arith_ss ++ wordsLib.WORD_ss) [IS_FIRST_BL_def, IS_SECOND_BL_def] mupp

val mupp3 = SPEC ``0x1b2w :word32`` (GEN ``p :word32`` mupp2);

val mupp4 = SIMP_RULE (arith_ss ++wordsLib.WORD_ss) [] mupp3

(*
 bdf0      (* 	pop	{r4, r5, r6, r7, pc} *)
 0001fff7  (*	.word	0x0001fff7 *)
*)

val BL_HOARE_THM = prove(``
   (SPEC M0_MODEL (
     ((~m0_NZCV) * (m0_COUNT (count :num)) * (m0_PC (p :word32)) * 
      (m0_MEMORY dmem m) * (m0_REG RName_LR r14) *
      (cond (m0_bl_pre (r14, count, dmem, m)) : (m0_component # m0_data -> bool) -> bool)))
     {(p, INL x); ((p+(2w :word32)), INL y)}
     ((~m0_NZCV) * (m0_COUNT (c + 2)) * (m0_PC (p+4w)) * (m0_MEMORY dmem m) * 
      (m0_REG RName_LR (p + (bl_offset x y)))
   ))
``,
cheat
);


val _ = export_theory();
