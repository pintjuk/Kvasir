
open HolKernel boolLib bossLib Parse;


(*
Run these if you are using interactive mode.

loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0/decompiler")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/common")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/hoare-triple")::(!loadPath));
loadPath := ("/home/luceat/Documents/skola/exjobb/Kvasir/playground/otp_scripts"::(!loadPath));
*)

open progTheory;
open m0_decompLib;
open helperLib;
open m0_progLib;
open otp_utilLib;

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

val _ = Theory.save_thm("m0_hoare_get_seq", m0_get_seq_no_th);
MOVE_TO_M0_CODE_POOL

DB.find "MOVE_TO_M0_CODE_POOL"
m0_prog.MOVE_TO_M0_CODE_POOL
Drule.SPECL [``(p+12w) :word32``, ``0x1fff7w :word32`` ] m0_progTheory.MOVE_TO_M0_CODE_POOL


val (m0_is_seq_in_order_th, m0_is_seq_in_order_defs) = m0_decompile "m0_is_seq_in_order" `
2300      (*	movs	r3, #0 *)
4281      (*	cmp	r1, r0 *)`

da04      (*	bge.n	148 <is_seq_in_order+0x10> *)
4a03      (*	ldr	r2, [pc, #12]	; (14c <is_seq_in_order+0x14>) *)

val m0_is_seq_in_order4_th = SPEC ``0x3ffew :word32`` (GEN ``w0 :word32`` (get_spec "4a02" []));
prove(``(DISJOINT
           (m0_instr (align 2 (pc + 4w) + 8w,data_to_thumb2 16382w))
           (m0_instr (pc,INL 18946w)))``,
  SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss++wordsLib.WORD_ss) 
            [m0_progTheory.data_to_thumb2_def, alignmentTheory.align_shift,
             m0_progTheory.m0_instr_def] >>
  BBLAST_TAC
);
REWRITE_RULE 

DB.match [] ``m0_instr``

DB.find "DISJOINT"

val (m0_is_seq_in_order1_th, m0_is_seq_in_order1_defs) = m0_decompile "m0_is_seq_in_order1" `
0003     (* 	movs	r3, r0 *)
2000     (* 	movs	r0, #0 *)
4299     (* 	cmp	r1, r3 *)`

da03     (* 	bge.n	164 <is_seq_in_order+0x10> *)

4a02     (* 	ldr	r2, [pc, #8]	; (168 <is_seq_in_order+0x14>) *)

val (m0_is_seq_in_order4_th, m0_is_seq_in_order4_defs) = m0_decompile "m0_is_seq_in_order4" `
429a     (* 	cmp	r2, r3 *)
4140     (* 	adcs	r0, r0 *)
b2c0     (* 	uxtb	r0, r0 *)`
4770     (* 	bx	lr *)
46c0     (* 	nop			; (mov r8, r8) *)`
00003ffe (*	.word	0x00003ffe *)`


(*
 b510   (* push	{r4, lr}	*)
*)

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


(* VALID_MSG FUNCTION, needs to be manually composed in mls *)

val m0_bx = m0_decompLib.m0_ABBREV_CALL "bx" (get_spec "4770" []);

val (m0_valid_msg1_th, m0_valid_msg1_defs) = m0_decompile "m0_valid_msg1" ` 
b5f8      	(* push	{r3, r4, r5, r6, r7, lr} *)
000d      	(* movs	r5, r1 *)
0016      	(* movs	r6, r2 *)
0007      	(* movs	r7, r0 *)`

(* f7ff ffe2 	 bl	17a <validate_seq_headers> *)
val (_, (bl_to_val_seqh, _, _), _) = (hd (m0_decompLib.m0_stage_1 "bl_to_val_seqh" `f7ff ffe2`));

val (m0_valid_msg2_th, m0_valid_msg2_defs) = m0_decompile "m0_valid_msg2" `
0004      	(* movs	r4, r0 *)
0038      	(* movs	r0, r7 *)`


(* f7ff ffe3 	bl	184 <validate_data_headers> *)
val (_, (bl_to_val_datah, _, _), _) = (hd (m0_decompLib.m0_stage_1 "bl_to_val_datah" `f7ff ffe3`));


val (m0_valid_msg3_th, m0_valid_msg3_defs) = m0_decompile "m0_valid_msg3" `
0031      	(* movs	r1, r6 *)
4004      	(* ands	r4, r0 *)
0028      	(* movs	r0, r5 *)`


(* f7ff ffb8 	 bl	138 <is_seq_in_order> *)
val (_, (bl_to_seq_order, _, _), _) = (hd (m0_decompLib.m0_stage_1 "bl_to_seq_order" `f7ff ffb8`));


val (m0_valid_msg3_th, m0_valid_msg3_defs) = m0_decompile "m0_valid_msg3" `
4020      	(* ands	r0, r4 *)`

(* Special handling of POP pc *)
(* bdf8      	 pop	{r3, r4, r5, r6, r7, pc} *)
val pop_from_valid_msg = m0_decompLib.m0_ABBREV_CALL "pop" (get_spec "bdf8" []);



(* 
val m0_valid_msg_th_abbrev = m0_decompLib.m0_ABBREV_CALL "new@" m0_valid_msg_th;
val m0_validate_seqh_th_abbrev = m0_decompLib.m0_ABBREV_CALL "new2@" m0_validate_seqh_th;

val compose_test = decompilerLib.SPEC_COMPOSE_RULE [m0_valid_msg_th_abbrev, 
                                                    bl_to_val_seqh, 
                                                    m0_validate_seqh_th_abbrev,
                                                    test_bx5];
val meh = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] compose_test
SIMP_RULE (std_ss++w2w_ss) [] compose_test;

val unabbrevd_compose = decompilerLib.UNABBREV_ALL compose_test

*)

(*
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
*)
(*
val (otp_process_messages1_th, otp_process_messages1_defs) = m0_decompile "m0_process_messages1"`
 (* b5f0 *)      (* 	push	{r4, r5, r6, r7, lr} *)
 2700      (* 	movs	r7, #0 *)
 b087      (* 	sub	sp, #28 *)
 9001      (* 	str	r0, [sp, #4] *)`;

open core_decompilerLib



val x = m0_decompLib.m0_stage_1 "btest" `e002`

val tst2 = SPEC_COMPOSE_RULE [thm1a, mupp4]

*)

val _ = export_theory();
