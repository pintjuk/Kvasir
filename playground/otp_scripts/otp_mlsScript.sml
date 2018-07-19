open HolKernel Parse boolLib bossLib


open wordsTheory;
open boolLib;
open pairLib;
open pred_setTheory;
open arithmeticTheory;



(*
Run these if you are using interactive mode.

loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0/decompiler")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/hoare-triple")::(!loadPath));
loadPath := ("/home/luceat/Documents/skola/exjobb/scripts"::(!loadPath));

*)

open helperLib;
open blastLib;
open m0_otp_decompTheory;

open otp_utilLib;

val _ = new_theory "otp_mls";

val mls_buffer_def = Define `
   (buffer (a :word32, count :num, dmem :word32->bool, mem :word32 -> word8) = 
      ~(a = 0w) /\ (a && 3w = 0w) /\ 
       ({a;a+1w;a+2w;a+3w;a+4w;a+5w;a+6w;a+7w;a+8w;a+9w} SUBSET dmem))`;


(* mid level spec for shifting buffer *)

val mls_shift_one_def = Define `mls_shift_one a m = 
     (m = (a =+ (7 >< 0) (a+1w)) m)`

val mls_shift_buffer_def = Define `
    shift_buffer a m = ((a += (7 >< 0) (a+1w)) m )


val mls_shift_buffer_def = Define `
    shift_buffer a (m :word32->word8) = ((a =+ m (a+1w)) 
                       (((a+1w) =+ m (a+2w))
                       (((a+2w) =+ m (a+3w))
                       (((a+3w) =+ m (a+4w))
                       (((a+4w) =+ m (a+5w))
                       (((a+5w) =+ m (a+6w))
                       (((a+6w) =+ m (a+7w))
                       (((a+7w) =+ m (a+8w))
                       (((a+8w) =+ m (a+9w))
                       (((a+9w) =+ 0w) m))))))))))`;

SIMP_RULE arith_ss [UPDATE_def] mls_shift_buffer_def;

val mls_shift_buffer_pre_th = prove(
    ``!a c dmem m. buffer(a, c, dmem, m) ==> m0_shift_buffer_pre(a, c, dmem, m)``,
    REWRITE_TAC [mls_buffer_def, m0_shift_buffer_pre_def] >>
    SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET]
);

val mls_add_rewr = prove(``! (w :word32) (v :word32). (w = w + v) <=> (0w = v)``,
   BBLAST_TAC
);

val mls_shift_buffer_post_exists_th = prove(
   ``!a count dmem m.
        ? r0 r3. 
        m0_shift_buffer(a, count, dmem, m) = 
        (r0, r3, count+39, dmem, shift_buffer a m)``,
   `! (b :word8). (7 >< 0) ((w2w b) :word32) = b` by BBLAST_TAC >>
   REWRITE_TAC [mls_shift_buffer_def, m0_shift_buffer_def] >>
   ASM_SIMP_TAC bool_ss [LET_DEF] >>
   SIMP_TAC (arith_ss ++ w2w_ss) [UPDATE_def, WORD_EQ_ADD_LCANCEL, WORD_ADD_COMM, mls_add_rewr] >>
   EVAL_TAC >>
   REWRITE_TAC [FUN_EQ_THM] >>
   BETA_TAC >>
   REPEAT STRIP_TAC >>
   REPEAT (COND_CASES_TAC >> 
      RULE_ASSUM_TAC GSYM >>
      ASM_SIMP_TAC arith_ss [WORD_EQ_ADD_LCANCEL, EQ_SYM, mls_add_rewr] >> 
      EVAL_TAC)
);

val mls_shift_buffer_post_th = POSTC_EXISTS_ELIM m0_shift_buffer_def mls_shift_buffer_post_exists_th;

val mls_shift_buffer = COMB_PREC_POSTC mls_shift_buffer_pre_th mls_shift_buffer_post_th;

val th = Theory.save_thm("otp_mls_shift_buffer",
  SIMP_RULE std_ss [LET_DEF] (INST_SPEC m0_hoare_shift mls_shift_buffer));


(* mid level spec for data header validation *)

val mls_six_or_def = Define `six_or x m = m (x+2w) || m (x+3w) || m (x+4w) || m (x+5w) ||
                            m (x+6w) || m (x+7w) || m (x+8w) || m (x+9w)`;

val mls_validate_datah_def = Define `validate_datah x m = ~(w2w (six_or x m) >>> 7)`;
                         
val otp_validate_datah_pre_th = prove(
   ``!a c dmem m . buffer(a, c, dmem, m) ==> m0_validate_datah_pre(a, c, dmem, m)``,
   ONCE_REWRITE_TAC [mls_buffer_def, m0_validate_datah_def, m0_validate_datah_pre_def, mls_validate_datah_def] >>
   SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET]
);

val otp_exists_post_th = prove(
   ``!a c dmem m . ? r1 r2.  m0_validate_datah(a, c, dmem, m)  = 
                  (validate_datah a m, r1, r2, c+26, dmem, m)``,
   REWRITE_TAC [mls_buffer_def, m0_validate_datah_def, mls_validate_datah_def, mls_six_or_def] >>
   REWRITE_TAC [LET_DEF, INSERT_SUBSET] >>
   SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET] >>
   SIMP_TAC arith_ss [WORD_w2w_OVER_BITWISE, WORD_OR_ASSOC] 
);

val otp_val_datah_post_th = POSTC_EXISTS_ELIM m0_validate_datah_def otp_exists_post_th;

val otp_validate_datah = COMB_PREC_POSTC otp_validate_datah_pre_th otp_val_datah_post_th;



val th = Theory.save_thm("otp_mls_validate_datah",
   SIMP_RULE std_ss [LET_DEF] (INST_SPEC m0_hoare_datah otp_validate_datah));



(* mid level spec for sequence number header validation *)

val mls_val_seqh_def = Define `validate_seqh x m = (w2w (m x && m (x+1w))) >>> 7` 

val otp_validate_seqh_pre = prove(
   ``!a c dmem m . buffer(a, c, dmem, m) ==>
        m0_validate_seqh_pre(a, c, dmem, m)``,
   ONCE_REWRITE_TAC [mls_buffer_def, m0_validate_seqh_pre_def] >>
   SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET]
);

val otp_validate_seqh_exists_post = prove (
   ``!a c dmem m. 
        ? r1 .
        m0_validate_seqh(a, c, dmem, m) = ((validate_seqh a m), r1, c+6, dmem, m)``,
    ONCE_REWRITE_TAC [mls_val_seqh_def, m0_validate_seqh_def] >>
    REPEAT STRIP_TAC >>
    SIMP_TAC arith_ss [LET_DEF, WORD_w2w_OVER_BITWISE, WORD_AND_COMM]
);

val otp_val_seqh_post_th = POSTC_EXISTS_ELIM m0_validate_seqh_def otp_validate_seqh_exists_post;

val otp_val_seqh = COMB_PREC_POSTC otp_validate_seqh_pre otp_val_seqh_post_th;

val th = save_thm("otp_mls_validate_seqh",
   SIMP_RULE std_ss [LET_DEF] (INST_SPEC m0_hoare_seqh otp_val_seqh));


mls_buffer_def

(* mid level spec for get sequence number *)

val mls_get_seq_no_def = Define `get_seq_no (x :word32) (m :word32->word8) :word32 = 
                                     ((w2w ((m x)) && 127w) << 7) + (w2w (m (x+1w)) && 127w)`;

val help_thm1 = prove(``!x. (x << 7 && 254w << 6 = (x && 127w) << 7)``,
  SIMP_TAC arith_ss [GSYM LSL_BITWISE, WORD_MUL_LSL]  >>
  BBLAST_TAC
);

val mls_get_seq_no_pre = prove(``!a c dmem m. buffer(a, c, dmem, m) ==>
                                    m0_get_seq_no_pre(a, c, dmem, m)``,
  ONCE_REWRITE_TAC[mls_buffer_def, m0_get_seq_no_pre_def] >>
  SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET]
);

val mls_get_seq_no_exists_post = prove(``!a c dmem m. ? r2 r3.
                             m0_get_seq_no(a, c, dmem, m) =
                                 (get_seq_no a m, r2, r3, (c+11), dmem, m)``,
  ONCE_REWRITE_TAC[m0_get_seq_no_def, mls_get_seq_no_def] >>
  SIMP_TAC arith_ss [LET_DEF, help_thm1, WORD_ADD_COMM]
);

val mls_get_seq_no_post = POSTC_EXISTS_ELIM m0_get_seq_no_def mls_get_seq_no_exists_post;

val mls_get_seq_no_th = COMB_PREC_POSTC mls_get_seq_no_pre mls_get_seq_no_post; 

val th = save_thm("otp_mls_get_seq_no",
   SIMP_RULE std_ss [LET_DEF] (INST_SPEC m0_hoare_get_seq mls_get_seq_no_th));


(* mid level spec for the buffer encryption *)
val mls_encrypt_def = Define `mls_encrypt buf key seq (m :word32->word8) =
                   (((buf+2w) =+ ((m (buf + 2w)) ?? (m (key + 8w*seq)))) 
                   (((buf+3w) =+ ((m (buf + 3w)) ?? (m (key + 8w*seq+1w)))) 
                   (((buf+4w) =+ ((m (buf + 4w)) ?? (m (key + 8w*seq+2w)))) 
                   (((buf+5w) =+ ((m (buf + 5w)) ?? (m (key + 8w*seq+3w)))) 
                   (((buf+6w) =+ ((m (buf + 6w)) ?? (m (key + 8w*seq+4w)))) 
                   (((buf+7w) =+ ((m (buf + 7w)) ?? (m (key + 8w*seq+5w)))) 
                   (((buf+8w) =+ ((m (buf + 8w)) ?? (m (key + 8w*seq+6w)))) 
                   (((buf+9w) =+ ((m (buf + 9w)) ?? (m (key + 8w*seq+7w)))) 
                                m))))))))`;    


val mls_encrypt_pre_th = prove(``!a c dmem m. buffer(a, c, dmem, m) ==>
                                   m0_encrypt_pre(r0, a, r2, r4, r13, r14, c, dmem, m)``,
   REWRITE_TAC [LET_DEF, m0_encrypt_pre_def, mls_buffer_def] >>
   SIMP_TAC arith_ss [LET_DEF, INSERT_SUBSET]
);

SIMP_RULE bool_ss [LET_DEF] m0_encrypt_pre_def


REWRITE_RULE [LET_DEF] m0_encrypt_pre

m0_encrypt_pre

m0_encrypt_def

m0_hoare_encrypt

(* mid level spec for zeroing the header of an encrypted buffer *)


(* Putting it all together *)

val _ = export_theory();
