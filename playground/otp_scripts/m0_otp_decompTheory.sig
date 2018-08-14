signature m0_otp_decompTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val bl_to_seq_order_m0_def : thm
    val bl_to_val_datah_m0_def : thm
    val bl_to_val_seqh_m0_def : thm
    val m0_encrypt : thm
    val m0_encrypt_m0_def : thm
    val m0_encrypt_pre : thm
    val m0_get_seq_no : thm
    val m0_get_seq_no_m0_def : thm
    val m0_get_seq_no_pre : thm
    val m0_shift_buffer : thm
    val m0_shift_buffer_m0_def : thm
    val m0_shift_buffer_pre : thm
    val m0_valid_msg1 : thm
    val m0_valid_msg1_m0_def : thm
    val m0_valid_msg1_pre : thm
    val m0_valid_msg2 : thm
    val m0_valid_msg2_m0_def : thm
    val m0_valid_msg2_pre : thm
    val m0_valid_msg3 : thm
    val m0_valid_msg3_m0_def : thm
    val m0_valid_msg3_pre : thm
    val m0_validate_datah : thm
    val m0_validate_datah_m0_def : thm
    val m0_validate_datah_pre : thm
    val m0_validate_seqh : thm
    val m0_validate_seqh_m0_def : thm
    val m0_validate_seqh_pre : thm
    val m0_zero_headers : thm
    val m0_zero_headers_m0_def : thm
    val m0_zero_headers_pre : thm

  (*  Theorems  *)
    val m0_encrypt_def : thm
    val m0_encrypt_pre_def : thm
    val m0_get_seq_no_def : thm
    val m0_get_seq_no_pre_def : thm
    val m0_hoare_datah : thm
    val m0_hoare_encrypt : thm
    val m0_hoare_get_seq : thm
    val m0_hoare_seqh : thm
    val m0_hoare_shift : thm
    val m0_hoare_zeroh : thm
    val m0_shift_buffer_def : thm
    val m0_shift_buffer_pre_def : thm
    val m0_valid_msg1_def : thm
    val m0_valid_msg1_pre_def : thm
    val m0_valid_msg2_def : thm
    val m0_valid_msg2_pre_def : thm
    val m0_valid_msg3_def : thm
    val m0_valid_msg3_pre_def : thm
    val m0_validate_datah_def : thm
    val m0_validate_datah_pre_def : thm
    val m0_validate_seqh_def : thm
    val m0_validate_seqh_pre_def : thm
    val m0_zero_headers_def : thm
    val m0_zero_headers_pre_def : thm

  val m0_otp_decomp_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [m0_decomp] Parent theory of "m0_otp_decomp"

   [bl_to_seq_order_m0_def]  Definition

       [] |- ∀p. bl_to_seq_order_m0 p = {(p,INR 0xF7FFFFB8w)}

   [bl_to_val_datah_m0_def]  Definition

       [] |- ∀p. bl_to_val_datah_m0 p = {(p,INR 0xF7FFFFE3w)}

   [bl_to_val_seqh_m0_def]  Definition

       [] |- ∀p. bl_to_val_seqh_m0 p = {(p,INR 0xF7FFFFE2w)}

   [m0_encrypt]  Definition

       []
      |- m0_encrypt =
         SHORT_TAILREC
           (λ(r0,r1,r2,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r0 = r0 ≪ 3 in
               let cond = GUARD 0 (r2 + s2@r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r4 = w2w (mem (r2 + s2@r0 )) in
               let cond = cond ∧ GUARD 0 (r1 + 2w ∈ dmem) in
               let s6@count = s4@count + 2 in
               let s6@r3 = w2w (mem (r1 + 2w)) in
               let s8@count = s6@count + 1 in
               let s8@r2 = r2 + s2@r0 in
               let s10@count = s8@count + 1 in
               let s10@r3 = s6@r3 ⊕ s4@r4 in
               let s12@count = s10@count + 2 in
               let s12@mem = (r1 + 2w =+ (7 >< 0) s10@r3 ) mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 1w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r0 = w2w (s12@mem (s8@r2 + 1w)) in
               let cond = cond ∧ GUARD 0 (r1 + 3w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r3 = w2w (s12@mem (r1 + 3w)) in
               let s18@count = s16@count + 1 in
               let s18@r3 = s16@r3 ⊕ s14@r0 in
               let s20@count = s18@count + 2 in
               let s20@mem = (r1 + 3w =+ (7 >< 0) s18@r3 ) s12@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 2w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r0 = w2w (s20@mem (s8@r2 + 2w)) in
               let cond = cond ∧ GUARD 0 (r1 + 4w ∈ dmem) in
               let s24@count = s22@count + 2 in
               let s24@r3 = w2w (s20@mem (r1 + 4w)) in
               let s26@count = s24@count + 1 in
               let s26@r3 = s24@r3 ⊕ s22@r0 in
               let s28@count = s26@count + 2 in
               let s28@mem = (r1 + 4w =+ (7 >< 0) s26@r3 ) s20@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 3w ∈ dmem) in
               let s30@count = s28@count + 2 in
               let s30@r0 = w2w (s28@mem (s8@r2 + 3w)) in
               let cond = cond ∧ GUARD 0 (r1 + 5w ∈ dmem) in
               let s32@count = s30@count + 2 in
               let s32@r3 = w2w (s28@mem (r1 + 5w)) in
               let s34@count = s32@count + 1 in
               let s34@r3 = s32@r3 ⊕ s30@r0 in
               let s36@count = s34@count + 2 in
               let s36@mem = (r1 + 5w =+ (7 >< 0) s34@r3 ) s28@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 4w ∈ dmem) in
               let s38@count = s36@count + 2 in
               let s38@r0 = w2w (s36@mem (s8@r2 + 4w)) in
               let cond = cond ∧ GUARD 0 (r1 + 6w ∈ dmem) in
               let s40@count = s38@count + 2 in
               let s40@r3 = w2w (s36@mem (r1 + 6w)) in
               let s42@count = s40@count + 1 in
               let s42@r3 = s40@r3 ⊕ s38@r0 in
               let s44@count = s42@count + 2 in
               let s44@mem = (r1 + 6w =+ (7 >< 0) s42@r3 ) s36@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 5w ∈ dmem) in
               let s46@count = s44@count + 2 in
               let s46@r0 = w2w (s44@mem (s8@r2 + 5w)) in
               let cond = cond ∧ GUARD 0 (r1 + 7w ∈ dmem) in
               let s48@count = s46@count + 2 in
               let s48@r3 = w2w (s44@mem (r1 + 7w)) in
               let s50@count = s48@count + 1 in
               let s50@r3 = s48@r3 ⊕ s46@r0 in
               let s52@count = s50@count + 2 in
               let s52@mem = (r1 + 7w =+ (7 >< 0) s50@r3 ) s44@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 6w ∈ dmem) in
               let s54@count = s52@count + 2 in
               let s54@r0 = w2w (s52@mem (s8@r2 + 6w)) in
               let cond = cond ∧ GUARD 0 (r1 + 8w ∈ dmem) in
               let s56@count = s54@count + 2 in
               let s56@r3 = w2w (s52@mem (r1 + 8w)) in
               let s58@count = s56@count + 1 in
               let s58@r3 = s56@r3 ⊕ s54@r0 in
               let s60@count = s58@count + 2 in
               let s60@mem = (r1 + 8w =+ (7 >< 0) s58@r3 ) s52@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 7w ∈ dmem) in
               let s62@count = s60@count + 2 in
               let s62@r2 = w2w (s60@mem (s8@r2 + 7w)) in
               let cond = cond ∧ GUARD 0 (r1 + 9w ∈ dmem) in
               let s64@count = s62@count + 2 in
               let s64@r3 = w2w (s60@mem (r1 + 9w)) in
               let s66@count = s64@count + 1 in
               let s66@r3 = s64@r3 ⊕ s62@r2 in
               let s68@count = s66@count + 2 in
               let s68@mem = (r1 + 9w =+ (7 >< 0) s66@r3 ) s60@mem
               in
                 (INR
                    (s54@r0 ,r1,s62@r2 ,s66@r3 ,s4@r4 ,s68@count ,dmem,
                     s68@mem ),cond)))

   [m0_encrypt_m0_def]  Definition

       []
      |- ∀p.
           m0_encrypt_m0 p =
           {(p,INL 192w); (p + 2w,INL 23572w); (p + 4w,INL 30859w);
            (p + 6w,INL 6162w); (p + 8w,INL 16483w); (p + 10w,INL 28811w);
            (p + 12w,INL 30800w); (p + 14w,INL 30923w);
            (p + 16w,INL 16451w); (p + 18w,INL 28875w);
            (p + 20w,INL 30864w); (p + 22w,INL 30987w);
            (p + 24w,INL 16451w); (p + 26w,INL 28939w);
            (p + 28w,INL 30928w); (p + 30w,INL 31051w);
            (p + 32w,INL 16451w); (p + 34w,INL 29003w);
            (p + 36w,INL 30992w); (p + 38w,INL 31115w);
            (p + 40w,INL 16451w); (p + 42w,INL 29067w);
            (p + 44w,INL 31056w); (p + 46w,INL 31179w);
            (p + 48w,INL 16451w); (p + 50w,INL 29131w);
            (p + 52w,INL 31120w); (p + 54w,INL 31243w);
            (p + 56w,INL 16451w); (p + 58w,INL 29195w);
            (p + 60w,INL 31186w); (p + 62w,INL 31307w);
            (p + 64w,INL 16467w); (p + 66w,INL 29259w)}

   [m0_encrypt_pre]  Definition

       []
      |- m0_encrypt_pre =
         SHORT_TAILREC_PRE
           (λ(r0,r1,r2,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r0 = r0 ≪ 3 in
               let cond = GUARD 0 (r2 + s2@r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r4 = w2w (mem (r2 + s2@r0 )) in
               let cond = cond ∧ GUARD 0 (r1 + 2w ∈ dmem) in
               let s6@count = s4@count + 2 in
               let s6@r3 = w2w (mem (r1 + 2w)) in
               let s8@count = s6@count + 1 in
               let s8@r2 = r2 + s2@r0 in
               let s10@count = s8@count + 1 in
               let s10@r3 = s6@r3 ⊕ s4@r4 in
               let s12@count = s10@count + 2 in
               let s12@mem = (r1 + 2w =+ (7 >< 0) s10@r3 ) mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 1w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r0 = w2w (s12@mem (s8@r2 + 1w)) in
               let cond = cond ∧ GUARD 0 (r1 + 3w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r3 = w2w (s12@mem (r1 + 3w)) in
               let s18@count = s16@count + 1 in
               let s18@r3 = s16@r3 ⊕ s14@r0 in
               let s20@count = s18@count + 2 in
               let s20@mem = (r1 + 3w =+ (7 >< 0) s18@r3 ) s12@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 2w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r0 = w2w (s20@mem (s8@r2 + 2w)) in
               let cond = cond ∧ GUARD 0 (r1 + 4w ∈ dmem) in
               let s24@count = s22@count + 2 in
               let s24@r3 = w2w (s20@mem (r1 + 4w)) in
               let s26@count = s24@count + 1 in
               let s26@r3 = s24@r3 ⊕ s22@r0 in
               let s28@count = s26@count + 2 in
               let s28@mem = (r1 + 4w =+ (7 >< 0) s26@r3 ) s20@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 3w ∈ dmem) in
               let s30@count = s28@count + 2 in
               let s30@r0 = w2w (s28@mem (s8@r2 + 3w)) in
               let cond = cond ∧ GUARD 0 (r1 + 5w ∈ dmem) in
               let s32@count = s30@count + 2 in
               let s32@r3 = w2w (s28@mem (r1 + 5w)) in
               let s34@count = s32@count + 1 in
               let s34@r3 = s32@r3 ⊕ s30@r0 in
               let s36@count = s34@count + 2 in
               let s36@mem = (r1 + 5w =+ (7 >< 0) s34@r3 ) s28@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 4w ∈ dmem) in
               let s38@count = s36@count + 2 in
               let s38@r0 = w2w (s36@mem (s8@r2 + 4w)) in
               let cond = cond ∧ GUARD 0 (r1 + 6w ∈ dmem) in
               let s40@count = s38@count + 2 in
               let s40@r3 = w2w (s36@mem (r1 + 6w)) in
               let s42@count = s40@count + 1 in
               let s42@r3 = s40@r3 ⊕ s38@r0 in
               let s44@count = s42@count + 2 in
               let s44@mem = (r1 + 6w =+ (7 >< 0) s42@r3 ) s36@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 5w ∈ dmem) in
               let s46@count = s44@count + 2 in
               let s46@r0 = w2w (s44@mem (s8@r2 + 5w)) in
               let cond = cond ∧ GUARD 0 (r1 + 7w ∈ dmem) in
               let s48@count = s46@count + 2 in
               let s48@r3 = w2w (s44@mem (r1 + 7w)) in
               let s50@count = s48@count + 1 in
               let s50@r3 = s48@r3 ⊕ s46@r0 in
               let s52@count = s50@count + 2 in
               let s52@mem = (r1 + 7w =+ (7 >< 0) s50@r3 ) s44@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 6w ∈ dmem) in
               let s54@count = s52@count + 2 in
               let s54@r0 = w2w (s52@mem (s8@r2 + 6w)) in
               let cond = cond ∧ GUARD 0 (r1 + 8w ∈ dmem) in
               let s56@count = s54@count + 2 in
               let s56@r3 = w2w (s52@mem (r1 + 8w)) in
               let s58@count = s56@count + 1 in
               let s58@r3 = s56@r3 ⊕ s54@r0 in
               let s60@count = s58@count + 2 in
               let s60@mem = (r1 + 8w =+ (7 >< 0) s58@r3 ) s52@mem in
               let cond = cond ∧ GUARD 0 (s8@r2 + 7w ∈ dmem) in
               let s62@count = s60@count + 2 in
               let s62@r2 = w2w (s60@mem (s8@r2 + 7w)) in
               let cond = cond ∧ GUARD 0 (r1 + 9w ∈ dmem) in
               let s64@count = s62@count + 2 in
               let s64@r3 = w2w (s60@mem (r1 + 9w)) in
               let s66@count = s64@count + 1 in
               let s66@r3 = s64@r3 ⊕ s62@r2 in
               let s68@count = s66@count + 2 in
               let s68@mem = (r1 + 9w =+ (7 >< 0) s66@r3 ) s60@mem
               in
                 (INR
                    (s54@r0 ,r1,s62@r2 ,s66@r3 ,s4@r4 ,s68@count ,dmem,
                     s68@mem ),cond)))

   [m0_get_seq_no]  Definition

       []
      |- m0_get_seq_no =
         SHORT_TAILREC
           (λ(r0,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r2 = 254w in
               let cond = GUARD 0 (r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r3 = w2w (mem r0) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s2@r2 ≪ 6 in
               let s8@count = s6@count + 1 in
               let s8@r3 = s4@r3 ≪ 7 in
               let s10@count = s8@count + 1 in
               let s10@r3 = s8@r3 && s6@r2 in
               let s12@count = s10@count + 1 in
               let s12@r2 = 127w in
               let cond = cond ∧ GUARD 0 (r0 + 1w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r0 = w2w (mem (r0 + 1w)) in
               let s16@count = s14@count + 1 in
               let s16@r0 = s14@r0 && s12@r2 in
               let s18@count = s16@count + 1 in
               let s18@r0 = s16@r0 + s10@r3
               in
                 (INR (s18@r0 ,s12@r2 ,s10@r3 ,s18@count ,dmem,mem),cond)))

   [m0_get_seq_no_m0_def]  Definition

       []
      |- ∀p.
           m0_get_seq_no_m0 p =
           {(p,INL 8958w); (p + 2w,INL 30723w); (p + 4w,INL 402w);
            (p + 6w,INL 475w); (p + 8w,INL 16403w); (p + 10w,INL 8831w);
            (p + 12w,INL 30784w); (p + 14w,INL 16400w);
            (p + 16w,INL 6336w)}

   [m0_get_seq_no_pre]  Definition

       []
      |- m0_get_seq_no_pre =
         SHORT_TAILREC_PRE
           (λ(r0,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r2 = 254w in
               let cond = GUARD 0 (r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r3 = w2w (mem r0) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s2@r2 ≪ 6 in
               let s8@count = s6@count + 1 in
               let s8@r3 = s4@r3 ≪ 7 in
               let s10@count = s8@count + 1 in
               let s10@r3 = s8@r3 && s6@r2 in
               let s12@count = s10@count + 1 in
               let s12@r2 = 127w in
               let cond = cond ∧ GUARD 0 (r0 + 1w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r0 = w2w (mem (r0 + 1w)) in
               let s16@count = s14@count + 1 in
               let s16@r0 = s14@r0 && s12@r2 in
               let s18@count = s16@count + 1 in
               let s18@r0 = s16@r0 + s10@r3
               in
                 (INR (s18@r0 ,s12@r2 ,s10@r3 ,s18@count ,dmem,mem),cond)))

   [m0_shift_buffer]  Definition

       []
      |- m0_shift_buffer =
         SHORT_TAILREC
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 + 1w ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem (r0 + 1w)) in
               let cond = cond ∧ GUARD 0 (r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@mem = (r0 =+ (7 >< 0) s2@r3 ) mem in
               let cond = cond ∧ GUARD 0 (r0 + 2w ∈ dmem) in
               let s6@count = s4@count + 2 in
               let s6@r3 = w2w (s4@mem (r0 + 2w)) in
               let s8@count = s6@count + 2 in
               let s8@mem = (r0 + 1w =+ (7 >< 0) s6@r3 ) s4@mem in
               let cond = cond ∧ GUARD 0 (r0 + 3w ∈ dmem) in
               let s10@count = s8@count + 2 in
               let s10@r3 = w2w (s8@mem (r0 + 3w)) in
               let s12@count = s10@count + 2 in
               let s12@mem = (r0 + 2w =+ (7 >< 0) s10@r3 ) s8@mem in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r3 = w2w (s12@mem (r0 + 4w)) in
               let s16@count = s14@count + 2 in
               let s16@mem = (r0 + 3w =+ (7 >< 0) s14@r3 ) s12@mem in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s18@count = s16@count + 2 in
               let s18@r3 = w2w (s16@mem (r0 + 5w)) in
               let s20@count = s18@count + 2 in
               let s20@mem = (r0 + 4w =+ (7 >< 0) s18@r3 ) s16@mem in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r3 = w2w (s20@mem (r0 + 6w)) in
               let s24@count = s22@count + 2 in
               let s24@mem = (r0 + 5w =+ (7 >< 0) s22@r3 ) s20@mem in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s26@count = s24@count + 2 in
               let s26@r3 = w2w (s24@mem (r0 + 7w)) in
               let s28@count = s26@count + 2 in
               let s28@mem = (r0 + 6w =+ (7 >< 0) s26@r3 ) s24@mem in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s30@count = s28@count + 2 in
               let s30@r3 = w2w (s28@mem (r0 + 8w)) in
               let s32@count = s30@count + 2 in
               let s32@mem = (r0 + 7w =+ (7 >< 0) s30@r3 ) s28@mem in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s34@count = s32@count + 2 in
               let s34@r3 = w2w (s32@mem (r0 + 9w)) in
               let s36@count = s34@count + 2 in
               let s36@mem = (r0 + 8w =+ (7 >< 0) s34@r3 ) s32@mem in
               let s38@count = s36@count + 1 in
               let s38@r3 = 0w in
               let s40@count = s38@count + 2 in
               let s40@mem = (r0 + 9w =+ (7 >< 0) s38@r3 ) s36@mem
               in
                 (INR (r0,s38@r3 ,s40@count ,dmem,s40@mem ),cond)))

   [m0_shift_buffer_m0_def]  Definition

       []
      |- ∀p.
           m0_shift_buffer_m0 p =
           {(p,INL 30787w); (p + 2w,INL 28675w); (p + 4w,INL 30851w);
            (p + 6w,INL 28739w); (p + 8w,INL 30915w); (p + 10w,INL 28803w);
            (p + 12w,INL 30979w); (p + 14w,INL 28867w);
            (p + 16w,INL 31043w); (p + 18w,INL 28931w);
            (p + 20w,INL 31107w); (p + 22w,INL 28995w);
            (p + 24w,INL 31171w); (p + 26w,INL 29059w);
            (p + 28w,INL 31235w); (p + 30w,INL 29123w);
            (p + 32w,INL 31299w); (p + 34w,INL 29187w);
            (p + 36w,INL 8960w); (p + 38w,INL 29251w)}

   [m0_shift_buffer_pre]  Definition

       []
      |- m0_shift_buffer_pre =
         SHORT_TAILREC_PRE
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 + 1w ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem (r0 + 1w)) in
               let cond = cond ∧ GUARD 0 (r0 ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@mem = (r0 =+ (7 >< 0) s2@r3 ) mem in
               let cond = cond ∧ GUARD 0 (r0 + 2w ∈ dmem) in
               let s6@count = s4@count + 2 in
               let s6@r3 = w2w (s4@mem (r0 + 2w)) in
               let s8@count = s6@count + 2 in
               let s8@mem = (r0 + 1w =+ (7 >< 0) s6@r3 ) s4@mem in
               let cond = cond ∧ GUARD 0 (r0 + 3w ∈ dmem) in
               let s10@count = s8@count + 2 in
               let s10@r3 = w2w (s8@mem (r0 + 3w)) in
               let s12@count = s10@count + 2 in
               let s12@mem = (r0 + 2w =+ (7 >< 0) s10@r3 ) s8@mem in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s14@count = s12@count + 2 in
               let s14@r3 = w2w (s12@mem (r0 + 4w)) in
               let s16@count = s14@count + 2 in
               let s16@mem = (r0 + 3w =+ (7 >< 0) s14@r3 ) s12@mem in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s18@count = s16@count + 2 in
               let s18@r3 = w2w (s16@mem (r0 + 5w)) in
               let s20@count = s18@count + 2 in
               let s20@mem = (r0 + 4w =+ (7 >< 0) s18@r3 ) s16@mem in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r3 = w2w (s20@mem (r0 + 6w)) in
               let s24@count = s22@count + 2 in
               let s24@mem = (r0 + 5w =+ (7 >< 0) s22@r3 ) s20@mem in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s26@count = s24@count + 2 in
               let s26@r3 = w2w (s24@mem (r0 + 7w)) in
               let s28@count = s26@count + 2 in
               let s28@mem = (r0 + 6w =+ (7 >< 0) s26@r3 ) s24@mem in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s30@count = s28@count + 2 in
               let s30@r3 = w2w (s28@mem (r0 + 8w)) in
               let s32@count = s30@count + 2 in
               let s32@mem = (r0 + 7w =+ (7 >< 0) s30@r3 ) s28@mem in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s34@count = s32@count + 2 in
               let s34@r3 = w2w (s32@mem (r0 + 9w)) in
               let s36@count = s34@count + 2 in
               let s36@mem = (r0 + 8w =+ (7 >< 0) s34@r3 ) s32@mem in
               let s38@count = s36@count + 1 in
               let s38@r3 = 0w in
               let s40@count = s38@count + 2 in
               let s40@mem = (r0 + 9w =+ (7 >< 0) s38@r3 ) s36@mem
               in
                 (INR (r0,s38@r3 ,s40@count ,dmem,s40@mem ),cond)))

   [m0_valid_msg1]  Definition

       []
      |- m0_valid_msg1 =
         SHORT_TAILREC
           (λ(r0,r1,r2,r3,r4,r5,r6,r7,r13,r14,count,dmem,mem).
              (let cond =
                     GUARD 0
                       (aligned 2 r13 ∧ r13 − 24w + 4w + 1w ∈ dmem ∧
                        r13 − 24w + 4w + 3w ∈ dmem ∧
                        r13 − 24w + 4w + 2w ∈ dmem ∧
                        r13 − 24w + 8w + 1w ∈ dmem ∧
                        r13 − 24w + 8w + 3w ∈ dmem ∧
                        r13 − 24w + 8w + 2w ∈ dmem ∧
                        r13 − 24w + 16w + 1w ∈ dmem ∧
                        r13 − 24w + 16w + 3w ∈ dmem ∧
                        r13 − 24w + 16w + 2w ∈ dmem ∧
                        r13 − 24w + 12w + 1w ∈ dmem ∧
                        r13 − 24w + 12w + 3w ∈ dmem ∧
                        r13 − 24w + 12w + 2w ∈ dmem ∧
                        r13 − 24w + 20w + 1w ∈ dmem ∧
                        r13 − 24w + 20w + 3w ∈ dmem ∧
                        r13 − 24w + 20w + 2w ∈ dmem ∧
                        r13 − 24w + 1w ∈ dmem ∧ r13 − 24w + 3w ∈ dmem ∧
                        r13 − 24w + 2w ∈ dmem ∧ r13 − 24w + 4w ∈ dmem ∧
                        r13 − 24w + 8w ∈ dmem ∧ r13 − 24w + 16w ∈ dmem ∧
                        r13 − 24w + 12w ∈ dmem ∧ r13 − 24w + 20w ∈ dmem ∧
                        r13 − 24w ∈ dmem)
               in
               let s2@count = count + 6 + 1 in
               let s2@mem =
                     (r13 − 24w =+ (7 >< 0) r3)
                       ((r13 − 24w + 1w =+ (15 >< 8) r3)
                          ((r13 − 24w + 2w =+ (23 >< 16) r3)
                             ((r13 − 24w + 3w =+ (31 >< 24) r3)
                                ((r13 − 24w + 4w =+ (7 >< 0) r4)
                                   ((r13 − 24w + 4w + 1w =+ (15 >< 8) r4)
                                      ((r13 − 24w + 4w + 2w =+
                                        (23 >< 16) r4)
                                         ((r13 − 24w + 4w + 3w =+
                                           (31 >< 24) r4)
                                            ((r13 − 24w + 8w =+
                                              (7 >< 0) r5)
                                               ((r13 − 24w + 8w + 1w =+
                                                 (15 >< 8) r5)
                                                  ((r13 − 24w + 8w + 2w =+
                                                    (23 >< 16) r5)
                                                     ((r13 − 24w + 8w +
                                                       3w =+ (31 >< 24) r5)
                                                        ((r13 − 24w +
                                                          12w =+
                                                          (7 >< 0) r6)
                                                           ((r13 − 24w +
                                                             12w + 1w =+
                                                             (15 >< 8) r6)
                                                              ((r13 − 24w +
                                                                12w + 2w =+
                                                                (23 >< 16)
                                                                  r6)
                                                                 ((r13 −
                                                                   24w +
                                                                   12w +
                                                                   3w =+
                                                                   (31 ><
                                                                    24) r6)
                                                                    ((r13 −
                                                                      24w +
                                                                      16w =+
                                                                      (7 ><
                                                                       0)
                                                                        r7)
                                                                       ((r13 −
                                                                         24w +
                                                                         16w +
                                                                         1w =+
                                                                         (15 ><
                                                                          8)
                                                                           r7)
                                                                          ((r13 −
                                                                            24w +
                                                                            16w +
                                                                            2w =+
                                                                            (23 ><
                                                                             16)
                                                                              r7)
                                                                             ((r13 −
                                                                               24w +
                                                                               16w +
                                                                               3w =+
                                                                               (31 ><
                                                                                24)
                                                                                 r7)
                                                                                ((r13 −
                                                                                  24w +
                                                                                  20w =+
                                                                                  (7 ><
                                                                                   0)
                                                                                    r14)
                                                                                   ((r13 −
                                                                                     24w +
                                                                                     20w +
                                                                                     1w =+
                                                                                     (15 ><
                                                                                      8)
                                                                                       r14)
                                                                                      ((r13 −
                                                                                        24w +
                                                                                        20w +
                                                                                        2w =+
                                                                                        (23 ><
                                                                                         16)
                                                                                          r14)
                                                                                         ((r13 −
                                                                                           24w +
                                                                                           20w +
                                                                                           3w =+
                                                                                           (31 ><
                                                                                            24)
                                                                                             r14)
                                                                                            mem)))))))))))))))))))))))
               in
               let s2@r13 = r13 − 24w && 0xFFFFFFFCw in
               let s4@count = s2@count + 1 in
               let s4@r5 = r1 in
               let s6@count = s4@count + 1 in
               let s6@r6 = r2 in
               let s8@count = s6@count + 1 in
               let s8@r7 = r0
               in
                 (INR
                    (r0,r1,r2,r3,r4,s4@r5 ,s6@r6 ,s8@r7 ,s2@r13 ,r14,
                     s8@count ,dmem,s2@mem ),cond)))

   [m0_valid_msg1_m0_def]  Definition

       []
      |- ∀p.
           m0_valid_msg1_m0 p =
           {(p,INL 46584w); (p + 2w,INL 13w); (p + 4w,INL 22w);
            (p + 6w,INL 7w)}

   [m0_valid_msg1_pre]  Definition

       []
      |- m0_valid_msg1_pre =
         SHORT_TAILREC_PRE
           (λ(r0,r1,r2,r3,r4,r5,r6,r7,r13,r14,count,dmem,mem).
              (let cond =
                     GUARD 0
                       (aligned 2 r13 ∧ r13 − 24w + 4w + 1w ∈ dmem ∧
                        r13 − 24w + 4w + 3w ∈ dmem ∧
                        r13 − 24w + 4w + 2w ∈ dmem ∧
                        r13 − 24w + 8w + 1w ∈ dmem ∧
                        r13 − 24w + 8w + 3w ∈ dmem ∧
                        r13 − 24w + 8w + 2w ∈ dmem ∧
                        r13 − 24w + 16w + 1w ∈ dmem ∧
                        r13 − 24w + 16w + 3w ∈ dmem ∧
                        r13 − 24w + 16w + 2w ∈ dmem ∧
                        r13 − 24w + 12w + 1w ∈ dmem ∧
                        r13 − 24w + 12w + 3w ∈ dmem ∧
                        r13 − 24w + 12w + 2w ∈ dmem ∧
                        r13 − 24w + 20w + 1w ∈ dmem ∧
                        r13 − 24w + 20w + 3w ∈ dmem ∧
                        r13 − 24w + 20w + 2w ∈ dmem ∧
                        r13 − 24w + 1w ∈ dmem ∧ r13 − 24w + 3w ∈ dmem ∧
                        r13 − 24w + 2w ∈ dmem ∧ r13 − 24w + 4w ∈ dmem ∧
                        r13 − 24w + 8w ∈ dmem ∧ r13 − 24w + 16w ∈ dmem ∧
                        r13 − 24w + 12w ∈ dmem ∧ r13 − 24w + 20w ∈ dmem ∧
                        r13 − 24w ∈ dmem)
               in
               let s2@count = count + 6 + 1 in
               let s2@mem =
                     (r13 − 24w =+ (7 >< 0) r3)
                       ((r13 − 24w + 1w =+ (15 >< 8) r3)
                          ((r13 − 24w + 2w =+ (23 >< 16) r3)
                             ((r13 − 24w + 3w =+ (31 >< 24) r3)
                                ((r13 − 24w + 4w =+ (7 >< 0) r4)
                                   ((r13 − 24w + 4w + 1w =+ (15 >< 8) r4)
                                      ((r13 − 24w + 4w + 2w =+
                                        (23 >< 16) r4)
                                         ((r13 − 24w + 4w + 3w =+
                                           (31 >< 24) r4)
                                            ((r13 − 24w + 8w =+
                                              (7 >< 0) r5)
                                               ((r13 − 24w + 8w + 1w =+
                                                 (15 >< 8) r5)
                                                  ((r13 − 24w + 8w + 2w =+
                                                    (23 >< 16) r5)
                                                     ((r13 − 24w + 8w +
                                                       3w =+ (31 >< 24) r5)
                                                        ((r13 − 24w +
                                                          12w =+
                                                          (7 >< 0) r6)
                                                           ((r13 − 24w +
                                                             12w + 1w =+
                                                             (15 >< 8) r6)
                                                              ((r13 − 24w +
                                                                12w + 2w =+
                                                                (23 >< 16)
                                                                  r6)
                                                                 ((r13 −
                                                                   24w +
                                                                   12w +
                                                                   3w =+
                                                                   (31 ><
                                                                    24) r6)
                                                                    ((r13 −
                                                                      24w +
                                                                      16w =+
                                                                      (7 ><
                                                                       0)
                                                                        r7)
                                                                       ((r13 −
                                                                         24w +
                                                                         16w +
                                                                         1w =+
                                                                         (15 ><
                                                                          8)
                                                                           r7)
                                                                          ((r13 −
                                                                            24w +
                                                                            16w +
                                                                            2w =+
                                                                            (23 ><
                                                                             16)
                                                                              r7)
                                                                             ((r13 −
                                                                               24w +
                                                                               16w +
                                                                               3w =+
                                                                               (31 ><
                                                                                24)
                                                                                 r7)
                                                                                ((r13 −
                                                                                  24w +
                                                                                  20w =+
                                                                                  (7 ><
                                                                                   0)
                                                                                    r14)
                                                                                   ((r13 −
                                                                                     24w +
                                                                                     20w +
                                                                                     1w =+
                                                                                     (15 ><
                                                                                      8)
                                                                                       r14)
                                                                                      ((r13 −
                                                                                        24w +
                                                                                        20w +
                                                                                        2w =+
                                                                                        (23 ><
                                                                                         16)
                                                                                          r14)
                                                                                         ((r13 −
                                                                                           24w +
                                                                                           20w +
                                                                                           3w =+
                                                                                           (31 ><
                                                                                            24)
                                                                                             r14)
                                                                                            mem)))))))))))))))))))))))
               in
               let s2@r13 = r13 − 24w && 0xFFFFFFFCw in
               let s4@count = s2@count + 1 in
               let s4@r5 = r1 in
               let s6@count = s4@count + 1 in
               let s6@r6 = r2 in
               let s8@count = s6@count + 1 in
               let s8@r7 = r0
               in
                 (INR
                    (r0,r1,r2,r3,r4,s4@r5 ,s6@r6 ,s8@r7 ,s2@r13 ,r14,
                     s8@count ,dmem,s2@mem ),cond)))

   [m0_valid_msg2]  Definition

       []
      |- m0_valid_msg2 =
         SHORT_TAILREC
           (λ(r0,r7,count).
              (let s2@count = count + 1 in
               let s2@r4 = r0 in
               let s4@count = s2@count + 1 in
               let s4@r0 = r7
               in
                 (INR (s4@r0 ,s2@r4 ,r7,s4@count ),T)))

   [m0_valid_msg2_m0_def]  Definition

       [] |- ∀p. m0_valid_msg2_m0 p = {(p,INL 4w); (p + 2w,INL 56w)}

   [m0_valid_msg2_pre]  Definition

       []
      |- m0_valid_msg2_pre =
         SHORT_TAILREC_PRE
           (λ(r0,r7,count).
              (let s2@count = count + 1 in
               let s2@r4 = r0 in
               let s4@count = s2@count + 1 in
               let s4@r0 = r7
               in
                 (INR (s4@r0 ,s2@r4 ,r7,s4@count ),T)))

   [m0_valid_msg3]  Definition

       []
      |- m0_valid_msg3 =
         SHORT_TAILREC
           (λ(r0,r4,count).
              (let s2@count = count + 1 in
               let s2@r0 = r0 && r4
               in
                 (INR (s2@r0 ,r4,s2@count ),T)))

   [m0_valid_msg3_m0_def]  Definition

       [] |- ∀p. m0_valid_msg3_m0 p = {(p,INL 16416w)}

   [m0_valid_msg3_pre]  Definition

       []
      |- m0_valid_msg3_pre =
         SHORT_TAILREC_PRE
           (λ(r0,r4,count).
              (let s2@count = count + 1 in
               let s2@r0 = r0 && r4
               in
                 (INR (s2@r0 ,r4,s2@count ),T)))

   [m0_validate_datah]  Definition

       []
      |- m0_validate_datah =
         SHORT_TAILREC
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 + 3w ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem (r0 + 3w)) in
               let cond = cond ∧ GUARD 0 (r0 + 2w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r2 = w2w (mem (r0 + 2w)) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s4@r2 ‖ s2@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s8@count = s6@count + 2 in
               let s8@r3 = w2w (mem (r0 + 4w)) in
               let s10@count = s8@count + 1 in
               let s10@r2 = s6@r2 ‖ s8@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s12@count = s10@count + 2 in
               let s12@r3 = w2w (mem (r0 + 5w)) in
               let s14@count = s12@count + 1 in
               let s14@r2 = s10@r2 ‖ s12@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r3 = w2w (mem (r0 + 6w)) in
               let s18@count = s16@count + 1 in
               let s18@r2 = s14@r2 ‖ s16@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s20@count = s18@count + 2 in
               let s20@r3 = w2w (mem (r0 + 7w)) in
               let s22@count = s20@count + 1 in
               let s22@r2 = s18@r2 ‖ s20@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s24@count = s22@count + 2 in
               let s24@r3 = w2w (mem (r0 + 8w)) in
               let s26@count = s24@count + 1 in
               let s26@r2 = s22@r2 ‖ s24@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s28@count = s26@count + 2 in
               let s28@r3 = w2w (mem (r0 + 9w)) in
               let s30@count = s28@count + 1 in
               let s30@r2 = s26@r2 ‖ s28@r3 in
               let s32@count = s30@count + 1 in
               let s32@r0 = ¬s30@r2 in
               let s34@count = s32@count + 1 in
               let s34@r0 = s30@r2 ⋙ 7 in
               let s36@count = s34@count + 1 in
               let s36@r0 = ¬s34@r0
               in
                 (INR (s36@r0 ,s30@r2 ,s28@r3 ,s36@count ,dmem,mem),cond)))

   [m0_validate_datah_m0_def]  Definition

       []
      |- ∀p.
           m0_validate_datah_m0 p =
           {(p,INL 30915w); (p + 2w,INL 30850w); (p + 4w,INL 17178w);
            (p + 6w,INL 30979w); (p + 8w,INL 17178w); (p + 10w,INL 31043w);
            (p + 12w,INL 17178w); (p + 14w,INL 31107w);
            (p + 16w,INL 17178w); (p + 18w,INL 31171w);
            (p + 20w,INL 17178w); (p + 22w,INL 31235w);
            (p + 24w,INL 17178w); (p + 26w,INL 31299w);
            (p + 28w,INL 17178w); (p + 30w,INL 17360w);
            (p + 32w,INL 2512w); (p + 34w,INL 17344w)}

   [m0_validate_datah_pre]  Definition

       []
      |- m0_validate_datah_pre =
         SHORT_TAILREC_PRE
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 + 3w ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem (r0 + 3w)) in
               let cond = cond ∧ GUARD 0 (r0 + 2w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r2 = w2w (mem (r0 + 2w)) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s4@r2 ‖ s2@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s8@count = s6@count + 2 in
               let s8@r3 = w2w (mem (r0 + 4w)) in
               let s10@count = s8@count + 1 in
               let s10@r2 = s6@r2 ‖ s8@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s12@count = s10@count + 2 in
               let s12@r3 = w2w (mem (r0 + 5w)) in
               let s14@count = s12@count + 1 in
               let s14@r2 = s10@r2 ‖ s12@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r3 = w2w (mem (r0 + 6w)) in
               let s18@count = s16@count + 1 in
               let s18@r2 = s14@r2 ‖ s16@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s20@count = s18@count + 2 in
               let s20@r3 = w2w (mem (r0 + 7w)) in
               let s22@count = s20@count + 1 in
               let s22@r2 = s18@r2 ‖ s20@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s24@count = s22@count + 2 in
               let s24@r3 = w2w (mem (r0 + 8w)) in
               let s26@count = s24@count + 1 in
               let s26@r2 = s22@r2 ‖ s24@r3 in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s28@count = s26@count + 2 in
               let s28@r3 = w2w (mem (r0 + 9w)) in
               let s30@count = s28@count + 1 in
               let s30@r2 = s26@r2 ‖ s28@r3 in
               let s32@count = s30@count + 1 in
               let s32@r0 = ¬s30@r2 in
               let s34@count = s32@count + 1 in
               let s34@r0 = s30@r2 ⋙ 7 in
               let s36@count = s34@count + 1 in
               let s36@r0 = ¬s34@r0
               in
                 (INR (s36@r0 ,s30@r2 ,s28@r3 ,s36@count ,dmem,mem),cond)))

   [m0_validate_seqh]  Definition

       []
      |- m0_validate_seqh =
         SHORT_TAILREC
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem r0) in
               let cond = cond ∧ GUARD 0 (r0 + 1w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r0 = w2w (mem (r0 + 1w)) in
               let s6@count = s4@count + 1 in
               let s6@r0 = s4@r0 && s2@r3 in
               let s8@count = s6@count + 1 in
               let s8@r0 = s6@r0 ⋙ 7
               in
                 (INR (s8@r0 ,s2@r3 ,s8@count ,dmem,mem),cond)))

   [m0_validate_seqh_m0_def]  Definition

       []
      |- ∀p.
           m0_validate_seqh_m0 p =
           {(p,INL 30723w); (p + 2w,INL 30784w); (p + 4w,INL 16408w);
            (p + 6w,INL 2496w)}

   [m0_validate_seqh_pre]  Definition

       []
      |- m0_validate_seqh_pre =
         SHORT_TAILREC_PRE
           (λ(r0,count,dmem,mem).
              (let cond = GUARD 0 (r0 ∈ dmem) in
               let s2@count = count + 2 in
               let s2@r3 = w2w (mem r0) in
               let cond = cond ∧ GUARD 0 (r0 + 1w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r0 = w2w (mem (r0 + 1w)) in
               let s6@count = s4@count + 1 in
               let s6@r0 = s4@r0 && s2@r3 in
               let s8@count = s6@count + 1 in
               let s8@r0 = s6@r0 ⋙ 7
               in
                 (INR (s8@r0 ,s2@r3 ,s8@count ,dmem,mem),cond)))

   [m0_zero_headers]  Definition

       []
      |- m0_zero_headers =
         SHORT_TAILREC
           (λ(r0,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r3 = 127w in
               let cond = GUARD 0 (r0 + 2w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r2 = w2w (mem (r0 + 2w)) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s4@r2 && s2@r3 in
               let s8@count = s6@count + 2 in
               let s8@mem = (r0 + 2w =+ (7 >< 0) s6@r2 ) mem in
               let cond = cond ∧ GUARD 0 (r0 + 3w ∈ dmem) in
               let s10@count = s8@count + 2 in
               let s10@r2 = w2w (s8@mem (r0 + 3w)) in
               let s12@count = s10@count + 1 in
               let s12@r2 = s10@r2 && s2@r3 in
               let s14@count = s12@count + 2 in
               let s14@mem = (r0 + 3w =+ (7 >< 0) s12@r2 ) s8@mem in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r2 = w2w (s14@mem (r0 + 4w)) in
               let s18@count = s16@count + 1 in
               let s18@r2 = s16@r2 && s2@r3 in
               let s20@count = s18@count + 2 in
               let s20@mem = (r0 + 4w =+ (7 >< 0) s18@r2 ) s14@mem in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r2 = w2w (s20@mem (r0 + 5w)) in
               let s24@count = s22@count + 1 in
               let s24@r2 = s22@r2 && s2@r3 in
               let s26@count = s24@count + 2 in
               let s26@mem = (r0 + 5w =+ (7 >< 0) s24@r2 ) s20@mem in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s28@count = s26@count + 2 in
               let s28@r2 = w2w (s26@mem (r0 + 6w)) in
               let s30@count = s28@count + 1 in
               let s30@r2 = s28@r2 && s2@r3 in
               let s32@count = s30@count + 2 in
               let s32@mem = (r0 + 6w =+ (7 >< 0) s30@r2 ) s26@mem in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s34@count = s32@count + 2 in
               let s34@r2 = w2w (s32@mem (r0 + 7w)) in
               let s36@count = s34@count + 1 in
               let s36@r2 = s34@r2 && s2@r3 in
               let s38@count = s36@count + 2 in
               let s38@mem = (r0 + 7w =+ (7 >< 0) s36@r2 ) s32@mem in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s40@count = s38@count + 2 in
               let s40@r2 = w2w (s38@mem (r0 + 8w)) in
               let s42@count = s40@count + 1 in
               let s42@r2 = s40@r2 && s2@r3 in
               let s44@count = s42@count + 2 in
               let s44@mem = (r0 + 8w =+ (7 >< 0) s42@r2 ) s38@mem in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s46@count = s44@count + 2 in
               let s46@r2 = w2w (s44@mem (r0 + 9w)) in
               let s48@count = s46@count + 1 in
               let s48@r3 = s2@r3 && s46@r2 in
               let s50@count = s48@count + 2 in
               let s50@mem = (r0 + 9w =+ (7 >< 0) s48@r3 ) s44@mem
               in
                 (INR (r0,s46@r2 ,s48@r3 ,s50@count ,dmem,s50@mem ),cond)))

   [m0_zero_headers_m0_def]  Definition

       []
      |- ∀p.
           m0_zero_headers_m0 p =
           {(p,INL 9087w); (p + 2w,INL 30850w); (p + 4w,INL 16410w);
            (p + 6w,INL 28802w); (p + 8w,INL 30914w); (p + 10w,INL 16410w);
            (p + 12w,INL 28866w); (p + 14w,INL 30978w);
            (p + 16w,INL 16410w); (p + 18w,INL 28930w);
            (p + 20w,INL 31042w); (p + 22w,INL 16410w);
            (p + 24w,INL 28994w); (p + 26w,INL 31106w);
            (p + 28w,INL 16410w); (p + 30w,INL 29058w);
            (p + 32w,INL 31170w); (p + 34w,INL 16410w);
            (p + 36w,INL 29122w); (p + 38w,INL 31234w);
            (p + 40w,INL 16410w); (p + 42w,INL 29186w);
            (p + 44w,INL 31298w); (p + 46w,INL 16403w);
            (p + 48w,INL 29251w)}

   [m0_zero_headers_pre]  Definition

       []
      |- m0_zero_headers_pre =
         SHORT_TAILREC_PRE
           (λ(r0,count,dmem,mem).
              (let s2@count = count + 1 in
               let s2@r3 = 127w in
               let cond = GUARD 0 (r0 + 2w ∈ dmem) in
               let s4@count = s2@count + 2 in
               let s4@r2 = w2w (mem (r0 + 2w)) in
               let s6@count = s4@count + 1 in
               let s6@r2 = s4@r2 && s2@r3 in
               let s8@count = s6@count + 2 in
               let s8@mem = (r0 + 2w =+ (7 >< 0) s6@r2 ) mem in
               let cond = cond ∧ GUARD 0 (r0 + 3w ∈ dmem) in
               let s10@count = s8@count + 2 in
               let s10@r2 = w2w (s8@mem (r0 + 3w)) in
               let s12@count = s10@count + 1 in
               let s12@r2 = s10@r2 && s2@r3 in
               let s14@count = s12@count + 2 in
               let s14@mem = (r0 + 3w =+ (7 >< 0) s12@r2 ) s8@mem in
               let cond = cond ∧ GUARD 0 (r0 + 4w ∈ dmem) in
               let s16@count = s14@count + 2 in
               let s16@r2 = w2w (s14@mem (r0 + 4w)) in
               let s18@count = s16@count + 1 in
               let s18@r2 = s16@r2 && s2@r3 in
               let s20@count = s18@count + 2 in
               let s20@mem = (r0 + 4w =+ (7 >< 0) s18@r2 ) s14@mem in
               let cond = cond ∧ GUARD 0 (r0 + 5w ∈ dmem) in
               let s22@count = s20@count + 2 in
               let s22@r2 = w2w (s20@mem (r0 + 5w)) in
               let s24@count = s22@count + 1 in
               let s24@r2 = s22@r2 && s2@r3 in
               let s26@count = s24@count + 2 in
               let s26@mem = (r0 + 5w =+ (7 >< 0) s24@r2 ) s20@mem in
               let cond = cond ∧ GUARD 0 (r0 + 6w ∈ dmem) in
               let s28@count = s26@count + 2 in
               let s28@r2 = w2w (s26@mem (r0 + 6w)) in
               let s30@count = s28@count + 1 in
               let s30@r2 = s28@r2 && s2@r3 in
               let s32@count = s30@count + 2 in
               let s32@mem = (r0 + 6w =+ (7 >< 0) s30@r2 ) s26@mem in
               let cond = cond ∧ GUARD 0 (r0 + 7w ∈ dmem) in
               let s34@count = s32@count + 2 in
               let s34@r2 = w2w (s32@mem (r0 + 7w)) in
               let s36@count = s34@count + 1 in
               let s36@r2 = s34@r2 && s2@r3 in
               let s38@count = s36@count + 2 in
               let s38@mem = (r0 + 7w =+ (7 >< 0) s36@r2 ) s32@mem in
               let cond = cond ∧ GUARD 0 (r0 + 8w ∈ dmem) in
               let s40@count = s38@count + 2 in
               let s40@r2 = w2w (s38@mem (r0 + 8w)) in
               let s42@count = s40@count + 1 in
               let s42@r2 = s40@r2 && s2@r3 in
               let s44@count = s42@count + 2 in
               let s44@mem = (r0 + 8w =+ (7 >< 0) s42@r2 ) s38@mem in
               let cond = cond ∧ GUARD 0 (r0 + 9w ∈ dmem) in
               let s46@count = s44@count + 2 in
               let s46@r2 = w2w (s44@mem (r0 + 9w)) in
               let s48@count = s46@count + 1 in
               let s48@r3 = s2@r3 && s46@r2 in
               let s50@count = s48@count + 2 in
               let s50@mem = (r0 + 9w =+ (7 >< 0) s48@r3 ) s44@mem
               in
                 (INR (r0,s46@r2 ,s48@r3 ,s50@count ,dmem,s50@mem ),cond)))

   [m0_encrypt_def]  Theorem

       []
      |- m0_encrypt (r0,r1,r2,count,dmem,mem) =
         (let count = count + 1 in
          let r0 = r0 ≪ 3 in
          let count = count + 2 in
          let r4 = w2w (mem (r2 + r0)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 2w)) in
          let count = count + 1 in
          let r2 = r2 + r0 in
          let count = count + 1 in
          let r3 = r3 ⊕ r4 in
          let count = count + 2 in
          let mem = (r1 + 2w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 1w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 3w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 3w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 2w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 4w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 4w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 3w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 5w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 5w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 4w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 6w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 6w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 5w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 7w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 7w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 6w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 8w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 8w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r2 + 7w)) in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 9w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r2 in
          let count = count + 2 in
          let mem = (r1 + 9w =+ (7 >< 0) r3) mem
          in
            (r0,r1,r2,r3,r4,count,dmem,mem))

   [m0_encrypt_pre_def]  Theorem

       []
      |- m0_encrypt_pre (r0,r1,r2,count,dmem,mem) ⇔
         (let count = count + 1 in
          let r0 = r0 ≪ 3 in
          let cond = r2 + r0 ∈ dmem in
          let count = count + 2 in
          let r4 = w2w (mem (r2 + r0)) in
          let cond = cond ∧ r1 + 2w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 2w)) in
          let count = count + 1 in
          let r2 = r2 + r0 in
          let count = count + 1 in
          let r3 = r3 ⊕ r4 in
          let count = count + 2 in
          let mem = (r1 + 2w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 1w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 1w)) in
          let cond = cond ∧ r1 + 3w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 3w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 3w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 2w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 2w)) in
          let cond = cond ∧ r1 + 4w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 4w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 4w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 3w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 3w)) in
          let cond = cond ∧ r1 + 5w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 5w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 5w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 4w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 4w)) in
          let cond = cond ∧ r1 + 6w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 6w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 6w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 5w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 5w)) in
          let cond = cond ∧ r1 + 7w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 7w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 7w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 6w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r2 + 6w)) in
          let cond = cond ∧ r1 + 8w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 8w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r0 in
          let count = count + 2 in
          let mem = (r1 + 8w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r2 + 7w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r2 + 7w)) in
          let cond = cond ∧ r1 + 9w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r1 + 9w)) in
          let count = count + 1 in
          let r3 = r3 ⊕ r2 in
          let count = count + 2 in
          let mem = (r1 + 9w =+ (7 >< 0) r3) mem
          in
            cond)

   [m0_get_seq_no_def]  Theorem

       []
      |- m0_get_seq_no (r0,count,dmem,mem) =
         (let count = count + 1 in
          let r2 = 254w in
          let count = count + 2 in
          let r3 = w2w (mem r0) in
          let count = count + 1 in
          let r2 = r2 ≪ 6 in
          let count = count + 1 in
          let r3 = r3 ≪ 7 in
          let count = count + 1 in
          let r3 = r3 && r2 in
          let count = count + 1 in
          let r2 = 127w in
          let count = count + 2 in
          let r0 = w2w (mem (r0 + 1w)) in
          let count = count + 1 in
          let r0 = r0 && r2 in
          let count = count + 1 in
          let r0 = r0 + r3
          in
            (r0,r2,r3,count,dmem,mem))

   [m0_get_seq_no_pre_def]  Theorem

       []
      |- m0_get_seq_no_pre (r0,count,dmem,mem) ⇔
         (let count = count + 1 in
          let r2 = 254w in
          let cond = r0 ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem r0) in
          let count = count + 1 in
          let r2 = r2 ≪ 6 in
          let count = count + 1 in
          let r3 = r3 ≪ 7 in
          let count = count + 1 in
          let r3 = r3 && r2 in
          let count = count + 1 in
          let r2 = 127w in
          let cond = cond ∧ r0 + 1w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r0 + 1w)) in
          let count = count + 1 in
          let r0 = r0 && r2 in
          let count = count + 1 in
          let r0 = r0 + r3
          in
            cond)

   [m0_hoare_datah]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_2 * ¬m0_REG RName_3 *
            cond (m0_validate_datah_pre (r0,count,dmem,mem)))
           {(p,INL 30915w); (p + 2w,INL 30850w); (p + 4w,INL 17178w);
            (p + 6w,INL 30979w); (p + 8w,INL 17178w); (p + 10w,INL 31043w);
            (p + 12w,INL 17178w); (p + 14w,INL 31107w);
            (p + 16w,INL 17178w); (p + 18w,INL 31171w);
            (p + 20w,INL 17178w); (p + 22w,INL 31235w);
            (p + 24w,INL 17178w); (p + 26w,INL 31299w);
            (p + 28w,INL 17178w); (p + 30w,INL 17360w);
            (p + 32w,INL 2512w); (p + 34w,INL 17344w)}
           (let (r0,r2,r3,count,dmem,mem) =
                  m0_validate_datah (r0,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 36w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_2 r2 *
              m0_REG RName_3 r3)

   [m0_hoare_encrypt]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * m0_REG RName_1 r1 * m0_REG RName_2 r2 *
            ¬m0_REG RName_3 * ¬m0_REG RName_4 *
            cond (m0_encrypt_pre (r0,r1,r2,count,dmem,mem)))
           {(p,INL 192w); (p + 2w,INL 23572w); (p + 4w,INL 30859w);
            (p + 6w,INL 6162w); (p + 8w,INL 16483w); (p + 10w,INL 28811w);
            (p + 12w,INL 30800w); (p + 14w,INL 30923w);
            (p + 16w,INL 16451w); (p + 18w,INL 28875w);
            (p + 20w,INL 30864w); (p + 22w,INL 30987w);
            (p + 24w,INL 16451w); (p + 26w,INL 28939w);
            (p + 28w,INL 30928w); (p + 30w,INL 31051w);
            (p + 32w,INL 16451w); (p + 34w,INL 29003w);
            (p + 36w,INL 30992w); (p + 38w,INL 31115w);
            (p + 40w,INL 16451w); (p + 42w,INL 29067w);
            (p + 44w,INL 31056w); (p + 46w,INL 31179w);
            (p + 48w,INL 16451w); (p + 50w,INL 29131w);
            (p + 52w,INL 31120w); (p + 54w,INL 31243w);
            (p + 56w,INL 16451w); (p + 58w,INL 29195w);
            (p + 60w,INL 31186w); (p + 62w,INL 31307w);
            (p + 64w,INL 16467w); (p + 66w,INL 29259w)}
           (let (r0,r1,r2,r3,r4,count,dmem,mem) =
                  m0_encrypt (r0,r1,r2,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 68w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_1 r1 *
              m0_REG RName_2 r2 * m0_REG RName_3 r3 * m0_REG RName_4 r4)

   [m0_hoare_get_seq]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_2 * ¬m0_REG RName_3 *
            cond (m0_get_seq_no_pre (r0,count,dmem,mem)))
           {(p,INL 8958w); (p + 2w,INL 30723w); (p + 4w,INL 402w);
            (p + 6w,INL 475w); (p + 8w,INL 16403w); (p + 10w,INL 8831w);
            (p + 12w,INL 30784w); (p + 14w,INL 16400w);
            (p + 16w,INL 6336w)}
           (let (r0,r2,r3,count,dmem,mem) =
                  m0_get_seq_no (r0,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 18w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_2 r2 *
              m0_REG RName_3 r3)

   [m0_hoare_seqh]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_3 *
            cond (m0_validate_seqh_pre (r0,count,dmem,mem)))
           {(p,INL 30723w); (p + 2w,INL 30784w); (p + 4w,INL 16408w);
            (p + 6w,INL 2496w)}
           (let (r0,r3,count,dmem,mem) =
                  m0_validate_seqh (r0,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 8w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_3 r3)

   [m0_hoare_shift]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_3 *
            cond (m0_shift_buffer_pre (r0,count,dmem,mem)))
           {(p,INL 30787w); (p + 2w,INL 28675w); (p + 4w,INL 30851w);
            (p + 6w,INL 28739w); (p + 8w,INL 30915w); (p + 10w,INL 28803w);
            (p + 12w,INL 30979w); (p + 14w,INL 28867w);
            (p + 16w,INL 31043w); (p + 18w,INL 28931w);
            (p + 20w,INL 31107w); (p + 22w,INL 28995w);
            (p + 24w,INL 31171w); (p + 26w,INL 29059w);
            (p + 28w,INL 31235w); (p + 30w,INL 29123w);
            (p + 32w,INL 31299w); (p + 34w,INL 29187w);
            (p + 36w,INL 8960w); (p + 38w,INL 29251w)}
           (let (r0,r3,count,dmem,mem) =
                  m0_shift_buffer (r0,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 40w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_3 r3)

   [m0_hoare_zeroh]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_2 * ¬m0_REG RName_3 *
            cond (m0_zero_headers_pre (r0,count,dmem,mem)))
           {(p,INL 9087w); (p + 2w,INL 30850w); (p + 4w,INL 16410w);
            (p + 6w,INL 28802w); (p + 8w,INL 30914w); (p + 10w,INL 16410w);
            (p + 12w,INL 28866w); (p + 14w,INL 30978w);
            (p + 16w,INL 16410w); (p + 18w,INL 28930w);
            (p + 20w,INL 31042w); (p + 22w,INL 16410w);
            (p + 24w,INL 28994w); (p + 26w,INL 31106w);
            (p + 28w,INL 16410w); (p + 30w,INL 29058w);
            (p + 32w,INL 31170w); (p + 34w,INL 16410w);
            (p + 36w,INL 29122w); (p + 38w,INL 31234w);
            (p + 40w,INL 16410w); (p + 42w,INL 29186w);
            (p + 44w,INL 31298w); (p + 46w,INL 16403w);
            (p + 48w,INL 29251w)}
           (let (r0,r2,r3,count,dmem,mem) =
                  m0_zero_headers (r0,count,dmem,mem)
            in
              ¬m0_NZCV * m0_COUNT count * m0_PC (p + 50w) *
              m0_MEMORY dmem mem * m0_REG RName_0 r0 * m0_REG RName_2 r2 *
              m0_REG RName_3 r3)

   [m0_shift_buffer_def]  Theorem

       []
      |- m0_shift_buffer (r0,count,dmem,mem) =
         (let count = count + 2 in
          let r3 = w2w (mem (r0 + 1w)) in
          let count = count + 2 in
          let mem = (r0 =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 2w)) in
          let count = count + 2 in
          let mem = (r0 + 1w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 3w)) in
          let count = count + 2 in
          let mem = (r0 + 2w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 4w)) in
          let count = count + 2 in
          let mem = (r0 + 3w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 5w)) in
          let count = count + 2 in
          let mem = (r0 + 4w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 6w)) in
          let count = count + 2 in
          let mem = (r0 + 5w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 7w)) in
          let count = count + 2 in
          let mem = (r0 + 6w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 8w)) in
          let count = count + 2 in
          let mem = (r0 + 7w =+ (7 >< 0) r3) mem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 9w)) in
          let count = count + 2 in
          let mem = (r0 + 8w =+ (7 >< 0) r3) mem in
          let count = count + 1 in
          let r3 = 0w in
          let count = count + 2 in
          let mem = (r0 + 9w =+ (7 >< 0) r3) mem
          in
            (r0,r3,count,dmem,mem))

   [m0_shift_buffer_pre_def]  Theorem

       []
      |- m0_shift_buffer_pre (r0,count,dmem,mem) ⇔
         (let cond = r0 + 1w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 1w)) in
          let cond = cond ∧ r0 ∈ dmem in
          let count = count + 2 in
          let mem = (r0 =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 2w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 2w)) in
          let count = count + 2 in
          let mem = (r0 + 1w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 3w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 3w)) in
          let count = count + 2 in
          let mem = (r0 + 2w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 4w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 4w)) in
          let count = count + 2 in
          let mem = (r0 + 3w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 5w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 5w)) in
          let count = count + 2 in
          let mem = (r0 + 4w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 6w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 6w)) in
          let count = count + 2 in
          let mem = (r0 + 5w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 7w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 7w)) in
          let count = count + 2 in
          let mem = (r0 + 6w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 8w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 8w)) in
          let count = count + 2 in
          let mem = (r0 + 7w =+ (7 >< 0) r3) mem in
          let cond = cond ∧ r0 + 9w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 9w)) in
          let count = count + 2 in
          let mem = (r0 + 8w =+ (7 >< 0) r3) mem in
          let count = count + 1 in
          let r3 = 0w in
          let count = count + 2 in
          let mem = (r0 + 9w =+ (7 >< 0) r3) mem
          in
            cond)

   [m0_valid_msg1_def]  Theorem

       []
      |- m0_valid_msg1 (r0,r1,r2,r3,r4,r5,r6,r7,r13,r14,count,dmem,mem) =
         (let count = count + 6 + 1 in
          let mem =
                (r13 − 24w =+ (7 >< 0) r3)
                  ((r13 − 24w + 1w =+ (15 >< 8) r3)
                     ((r13 − 24w + 2w =+ (23 >< 16) r3)
                        ((r13 − 24w + 3w =+ (31 >< 24) r3)
                           ((r13 − 24w + 4w =+ (7 >< 0) r4)
                              ((r13 − 24w + 4w + 1w =+ (15 >< 8) r4)
                                 ((r13 − 24w + 4w + 2w =+ (23 >< 16) r4)
                                    ((r13 − 24w + 4w + 3w =+ (31 >< 24) r4)
                                       ((r13 − 24w + 8w =+ (7 >< 0) r5)
                                          ((r13 − 24w + 8w + 1w =+
                                            (15 >< 8) r5)
                                             ((r13 − 24w + 8w + 2w =+
                                               (23 >< 16) r5)
                                                ((r13 − 24w + 8w + 3w =+
                                                  (31 >< 24) r5)
                                                   ((r13 − 24w + 12w =+
                                                     (7 >< 0) r6)
                                                      ((r13 − 24w + 12w +
                                                        1w =+ (15 >< 8) r6)
                                                         ((r13 − 24w +
                                                           12w + 2w =+
                                                           (23 >< 16) r6)
                                                            ((r13 − 24w +
                                                              12w + 3w =+
                                                              (31 >< 24)
                                                                r6)
                                                               ((r13 −
                                                                 24w +
                                                                 16w =+
                                                                 (7 >< 0)
                                                                   r7)
                                                                  ((r13 −
                                                                    24w +
                                                                    16w +
                                                                    1w =+
                                                                    (15 ><
                                                                     8) r7)
                                                                     ((r13 −
                                                                       24w +
                                                                       16w +
                                                                       2w =+
                                                                       (23 ><
                                                                        16)
                                                                         r7)
                                                                        ((r13 −
                                                                          24w +
                                                                          16w +
                                                                          3w =+
                                                                          (31 ><
                                                                           24)
                                                                            r7)
                                                                           ((r13 −
                                                                             24w +
                                                                             20w =+
                                                                             (7 ><
                                                                              0)
                                                                               r14)
                                                                              ((r13 −
                                                                                24w +
                                                                                20w +
                                                                                1w =+
                                                                                (15 ><
                                                                                 8)
                                                                                  r14)
                                                                                 ((r13 −
                                                                                   24w +
                                                                                   20w +
                                                                                   2w =+
                                                                                   (23 ><
                                                                                    16)
                                                                                     r14)
                                                                                    ((r13 −
                                                                                      24w +
                                                                                      20w +
                                                                                      3w =+
                                                                                      (31 ><
                                                                                       24)
                                                                                        r14)
                                                                                       mem)))))))))))))))))))))))
          in
          let r13 = r13 − 24w && 0xFFFFFFFCw in
          let count = count + 1 in
          let r5 = r1 in
          let count = count + 1 in
          let r6 = r2 in
          let count = count + 1 in
          let r7 = r0
          in
            (r0,r1,r2,r3,r4,r5,r6,r7,r13,r14,count,dmem,mem))

   [m0_valid_msg1_pre_def]  Theorem

       []
      |- m0_valid_msg1_pre
           (r0,r1,r2,r3,r4,r5,r6,r7,r13,r14,count,dmem,mem) ⇔
         (let cond =
                aligned 2 r13 ∧ r13 − 24w + 4w + 1w ∈ dmem ∧
                r13 − 24w + 4w + 3w ∈ dmem ∧ r13 − 24w + 4w + 2w ∈ dmem ∧
                r13 − 24w + 8w + 1w ∈ dmem ∧ r13 − 24w + 8w + 3w ∈ dmem ∧
                r13 − 24w + 8w + 2w ∈ dmem ∧ r13 − 24w + 16w + 1w ∈ dmem ∧
                r13 − 24w + 16w + 3w ∈ dmem ∧ r13 − 24w + 16w + 2w ∈ dmem ∧
                r13 − 24w + 12w + 1w ∈ dmem ∧ r13 − 24w + 12w + 3w ∈ dmem ∧
                r13 − 24w + 12w + 2w ∈ dmem ∧ r13 − 24w + 20w + 1w ∈ dmem ∧
                r13 − 24w + 20w + 3w ∈ dmem ∧ r13 − 24w + 20w + 2w ∈ dmem ∧
                r13 − 24w + 1w ∈ dmem ∧ r13 − 24w + 3w ∈ dmem ∧
                r13 − 24w + 2w ∈ dmem ∧ r13 − 24w + 4w ∈ dmem ∧
                r13 − 24w + 8w ∈ dmem ∧ r13 − 24w + 16w ∈ dmem ∧
                r13 − 24w + 12w ∈ dmem ∧ r13 − 24w + 20w ∈ dmem ∧
                r13 − 24w ∈ dmem
          in
          let count = count + 6 + 1 in
          let mem =
                (r13 − 24w =+ (7 >< 0) r3)
                  ((r13 − 24w + 1w =+ (15 >< 8) r3)
                     ((r13 − 24w + 2w =+ (23 >< 16) r3)
                        ((r13 − 24w + 3w =+ (31 >< 24) r3)
                           ((r13 − 24w + 4w =+ (7 >< 0) r4)
                              ((r13 − 24w + 4w + 1w =+ (15 >< 8) r4)
                                 ((r13 − 24w + 4w + 2w =+ (23 >< 16) r4)
                                    ((r13 − 24w + 4w + 3w =+ (31 >< 24) r4)
                                       ((r13 − 24w + 8w =+ (7 >< 0) r5)
                                          ((r13 − 24w + 8w + 1w =+
                                            (15 >< 8) r5)
                                             ((r13 − 24w + 8w + 2w =+
                                               (23 >< 16) r5)
                                                ((r13 − 24w + 8w + 3w =+
                                                  (31 >< 24) r5)
                                                   ((r13 − 24w + 12w =+
                                                     (7 >< 0) r6)
                                                      ((r13 − 24w + 12w +
                                                        1w =+ (15 >< 8) r6)
                                                         ((r13 − 24w +
                                                           12w + 2w =+
                                                           (23 >< 16) r6)
                                                            ((r13 − 24w +
                                                              12w + 3w =+
                                                              (31 >< 24)
                                                                r6)
                                                               ((r13 −
                                                                 24w +
                                                                 16w =+
                                                                 (7 >< 0)
                                                                   r7)
                                                                  ((r13 −
                                                                    24w +
                                                                    16w +
                                                                    1w =+
                                                                    (15 ><
                                                                     8) r7)
                                                                     ((r13 −
                                                                       24w +
                                                                       16w +
                                                                       2w =+
                                                                       (23 ><
                                                                        16)
                                                                         r7)
                                                                        ((r13 −
                                                                          24w +
                                                                          16w +
                                                                          3w =+
                                                                          (31 ><
                                                                           24)
                                                                            r7)
                                                                           ((r13 −
                                                                             24w +
                                                                             20w =+
                                                                             (7 ><
                                                                              0)
                                                                               r14)
                                                                              ((r13 −
                                                                                24w +
                                                                                20w +
                                                                                1w =+
                                                                                (15 ><
                                                                                 8)
                                                                                  r14)
                                                                                 ((r13 −
                                                                                   24w +
                                                                                   20w +
                                                                                   2w =+
                                                                                   (23 ><
                                                                                    16)
                                                                                     r14)
                                                                                    ((r13 −
                                                                                      24w +
                                                                                      20w +
                                                                                      3w =+
                                                                                      (31 ><
                                                                                       24)
                                                                                        r14)
                                                                                       mem)))))))))))))))))))))))
          in
          let r13 = r13 − 24w && 0xFFFFFFFCw in
          let count = count + 1 in
          let r5 = r1 in
          let count = count + 1 in
          let r6 = r2 in
          let count = count + 1 in
          let r7 = r0
          in
            cond)

   [m0_valid_msg2_def]  Theorem

       []
      |- m0_valid_msg2 (r0,r7,count) =
         (let count = count + 1 in
          let r4 = r0 in
          let count = count + 1 in
          let r0 = r7
          in
            (r0,r4,r7,count))

   [m0_valid_msg2_pre_def]  Theorem

       []
      |- m0_valid_msg2_pre (r0,r7,count) ⇔
         (let count = count + 1 in
          let r4 = r0 in
          let count = count + 1 in
          let r0 = r7
          in
            T)

   [m0_valid_msg3_def]  Theorem

       []
      |- m0_valid_msg3 (r0,r4,count) =
         (let count = count + 1 in let r0 = r0 && r4 in (r0,r4,count))

   [m0_valid_msg3_pre_def]  Theorem

       []
      |- m0_valid_msg3_pre (r0,r4,count) ⇔
         (let count = count + 1 in let r0 = r0 && r4 in T)

   [m0_validate_datah_def]  Theorem

       []
      |- m0_validate_datah (r0,count,dmem,mem) =
         (let count = count + 2 in
          let r3 = w2w (mem (r0 + 3w)) in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 2w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 4w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 5w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 6w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 7w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 8w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 9w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 1 in
          let r0 = ¬r2 in
          let count = count + 1 in
          let r0 = r2 ⋙ 7 in
          let count = count + 1 in
          let r0 = ¬r0
          in
            (r0,r2,r3,count,dmem,mem))

   [m0_validate_datah_pre_def]  Theorem

       []
      |- m0_validate_datah_pre (r0,count,dmem,mem) ⇔
         (let cond = r0 + 3w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 3w)) in
          let cond = cond ∧ r0 + 2w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 2w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 4w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 4w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 5w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 5w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 6w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 6w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 7w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 7w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 8w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 8w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let cond = cond ∧ r0 + 9w ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem (r0 + 9w)) in
          let count = count + 1 in
          let r2 = r2 ‖ r3 in
          let count = count + 1 in
          let r0 = ¬r2 in
          let count = count + 1 in
          let r0 = r2 ⋙ 7 in
          let count = count + 1 in
          let r0 = ¬r0
          in
            cond)

   [m0_validate_seqh_def]  Theorem

       []
      |- m0_validate_seqh (r0,count,dmem,mem) =
         (let count = count + 2 in
          let r3 = w2w (mem r0) in
          let count = count + 2 in
          let r0 = w2w (mem (r0 + 1w)) in
          let count = count + 1 in
          let r0 = r0 && r3 in
          let count = count + 1 in
          let r0 = r0 ⋙ 7
          in
            (r0,r3,count,dmem,mem))

   [m0_validate_seqh_pre_def]  Theorem

       []
      |- m0_validate_seqh_pre (r0,count,dmem,mem) ⇔
         (let cond = r0 ∈ dmem in
          let count = count + 2 in
          let r3 = w2w (mem r0) in
          let cond = cond ∧ r0 + 1w ∈ dmem in
          let count = count + 2 in
          let r0 = w2w (mem (r0 + 1w)) in
          let count = count + 1 in
          let r0 = r0 && r3 in
          let count = count + 1 in
          let r0 = r0 ⋙ 7
          in
            cond)

   [m0_zero_headers_def]  Theorem

       []
      |- m0_zero_headers (r0,count,dmem,mem) =
         (let count = count + 1 in
          let r3 = 127w in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 2w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 2w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 3w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 3w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 4w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 4w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 5w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 5w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 6w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 6w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 7w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 7w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 8w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 8w =+ (7 >< 0) r2) mem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 9w)) in
          let count = count + 1 in
          let r3 = r3 && r2 in
          let count = count + 2 in
          let mem = (r0 + 9w =+ (7 >< 0) r3) mem
          in
            (r0,r2,r3,count,dmem,mem))

   [m0_zero_headers_pre_def]  Theorem

       []
      |- m0_zero_headers_pre (r0,count,dmem,mem) ⇔
         (let count = count + 1 in
          let r3 = 127w in
          let cond = r0 + 2w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 2w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 2w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 3w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 3w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 3w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 4w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 4w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 4w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 5w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 5w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 5w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 6w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 6w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 6w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 7w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 7w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 7w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 8w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 8w)) in
          let count = count + 1 in
          let r2 = r2 && r3 in
          let count = count + 2 in
          let mem = (r0 + 8w =+ (7 >< 0) r2) mem in
          let cond = cond ∧ r0 + 9w ∈ dmem in
          let count = count + 2 in
          let r2 = w2w (mem (r0 + 9w)) in
          let count = count + 1 in
          let r3 = r3 && r2 in
          let count = count + 2 in
          let mem = (r0 + 9w =+ (7 >< 0) r3) mem
          in
            cond)


*)
end
