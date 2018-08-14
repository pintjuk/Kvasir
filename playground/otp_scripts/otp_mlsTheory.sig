signature otp_mlsTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val buffer_def : thm
    val get_seq_no_def : thm
    val mls_encrypt_def : thm
    val mls_shift_one_def : thm
    val shift_buffer_def : thm
    val six_or_def : thm
    val validate_datah_def : thm
    val validate_seqh_def : thm

  (*  Theorems  *)
    val otp_mls_get_seq_no : thm
    val otp_mls_shift_buffer : thm
    val otp_mls_validate_datah : thm
    val otp_mls_validate_seqh : thm

  val otp_mls_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [m0_otp_decomp] Parent theory of "otp_mls"

   [buffer_def]  Definition

       []
      |- ∀a count dmem mem.
           buffer (a,count,dmem,mem) ⇔
           a ≠ 0w ∧ (a && 3w = 0w) ∧
           {a; a + 1w; a + 2w; a + 3w; a + 4w; a + 5w; a + 6w; a + 7w;
            a + 8w; a + 9w} ⊆ dmem

   [get_seq_no_def]  Definition

       []
      |- ∀x m.
           get_seq_no x m =
           (w2w (m x) && 127w) ≪ 7 + (w2w (m (x + 1w)) && 127w)

   [mls_encrypt_def]  Definition

       []
      |- ∀buf key seq m.
           mls_encrypt buf key seq m =
           (buf + 2w =+ m (buf + 2w) ⊕ m (key + 8w * seq))
             ((buf + 3w =+ m (buf + 3w) ⊕ m (key + 8w * seq + 1w))
                ((buf + 4w =+ m (buf + 4w) ⊕ m (key + 8w * seq + 2w))
                   ((buf + 5w =+ m (buf + 5w) ⊕ m (key + 8w * seq + 3w))
                      ((buf + 6w =+ m (buf + 6w) ⊕ m (key + 8w * seq + 4w))
                         ((buf + 7w =+
                           m (buf + 7w) ⊕ m (key + 8w * seq + 5w))
                            ((buf + 8w =+
                              m (buf + 8w) ⊕ m (key + 8w * seq + 6w))
                               ((buf + 9w =+
                                 m (buf + 9w) ⊕ m (key + 8w * seq + 7w))
                                  m)))))))

   [mls_shift_one_def]  Definition

       [] |- ∀a m. mls_shift_one a m ⇔ (m = (a =+ (7 >< 0) (a + 1w)) m)

   [shift_buffer_def]  Definition

       []
      |- ∀a m.
           shift_buffer a m =
           (a =+ m (a + 1w))
             ((a + 1w =+ m (a + 2w))
                ((a + 2w =+ m (a + 3w))
                   ((a + 3w =+ m (a + 4w))
                      ((a + 4w =+ m (a + 5w))
                         ((a + 5w =+ m (a + 6w))
                            ((a + 6w =+ m (a + 7w))
                               ((a + 7w =+ m (a + 8w))
                                  ((a + 8w =+ m (a + 9w))
                                     ((a + 9w =+ 0w) m)))))))))

   [six_or_def]  Definition

       []
      |- ∀x m.
           six_or x m =
           m (x + 2w) ‖ m (x + 3w) ‖ m (x + 4w) ‖ m (x + 5w) ‖ m (x + 6w) ‖
           m (x + 7w) ‖ m (x + 8w) ‖ m (x + 9w)

   [validate_datah_def]  Definition

       [] |- ∀x m. validate_datah x m = ¬(w2w (six_or x m) ⋙ 7)

   [validate_seqh_def]  Definition

       [] |- ∀x m. validate_seqh x m = w2w (m x && m (x + 1w)) ⋙ 7

   [otp_mls_get_seq_no]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_2 * ¬m0_REG RName_3 *
            cond (buffer (r0,count,dmem,mem)))
           {(p,INL 8958w); (p + 2w,INL 30723w); (p + 4w,INL 402w);
            (p + 6w,INL 475w); (p + 8w,INL 16403w); (p + 10w,INL 8831w);
            (p + 12w,INL 30784w); (p + 14w,INL 16400w);
            (p + 16w,INL 6336w)}
           (¬m0_NZCV * m0_COUNT (count + 11) * m0_PC (p + 18w) *
            m0_MEMORY dmem mem * m0_REG RName_0 (get_seq_no r0 mem) *
            m0_REG RName_2 127w *
            m0_REG RName_3 (w2w (mem r0) ≪ 7 && 254w ≪ 6))

   [otp_mls_shift_buffer]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_3 *
            cond (buffer (r0,count,dmem,mem)))
           {(p,INL 30787w); (p + 2w,INL 28675w); (p + 4w,INL 30851w);
            (p + 6w,INL 28739w); (p + 8w,INL 30915w); (p + 10w,INL 28803w);
            (p + 12w,INL 30979w); (p + 14w,INL 28867w);
            (p + 16w,INL 31043w); (p + 18w,INL 28931w);
            (p + 20w,INL 31107w); (p + 22w,INL 28995w);
            (p + 24w,INL 31171w); (p + 26w,INL 29059w);
            (p + 28w,INL 31235w); (p + 30w,INL 29123w);
            (p + 32w,INL 31299w); (p + 34w,INL 29187w);
            (p + 36w,INL 8960w); (p + 38w,INL 29251w)}
           (¬m0_NZCV * m0_COUNT (count + 39) * m0_PC (p + 40w) *
            m0_MEMORY dmem (shift_buffer r0 mem) * m0_REG RName_0 r0 *
            m0_REG RName_3 0w)

   [otp_mls_validate_datah]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_2 * ¬m0_REG RName_3 *
            cond (buffer (r0,count,dmem,mem)))
           {(p,INL 30915w); (p + 2w,INL 30850w); (p + 4w,INL 17178w);
            (p + 6w,INL 30979w); (p + 8w,INL 17178w); (p + 10w,INL 31043w);
            (p + 12w,INL 17178w); (p + 14w,INL 31107w);
            (p + 16w,INL 17178w); (p + 18w,INL 31171w);
            (p + 20w,INL 17178w); (p + 22w,INL 31235w);
            (p + 24w,INL 17178w); (p + 26w,INL 31299w);
            (p + 28w,INL 17178w); (p + 30w,INL 17360w);
            (p + 32w,INL 2512w); (p + 34w,INL 17344w)}
           (¬m0_NZCV * m0_COUNT (count + 26) * m0_PC (p + 36w) *
            m0_MEMORY dmem mem * m0_REG RName_0 (validate_datah r0 mem) *
            m0_REG RName_2
              (w2w
                 (mem (r0 + 2w) ‖ mem (r0 + 3w) ‖ mem (r0 + 4w) ‖
                  mem (r0 + 5w) ‖ mem (r0 + 6w) ‖ mem (r0 + 7w) ‖
                  mem (r0 + 8w) ‖ mem (r0 + 9w))) *
            m0_REG RName_3 (w2w (mem (r0 + 9w))))

   [otp_mls_validate_seqh]  Theorem

       []
      |- SPEC M0_MODEL
           (¬m0_NZCV * m0_COUNT count * m0_PC p * m0_MEMORY dmem mem *
            m0_REG RName_0 r0 * ¬m0_REG RName_3 *
            cond (buffer (r0,count,dmem,mem)))
           {(p,INL 30723w); (p + 2w,INL 30784w); (p + 4w,INL 16408w);
            (p + 6w,INL 2496w)}
           (¬m0_NZCV * m0_COUNT (count + 6) * m0_PC (p + 8w) *
            m0_MEMORY dmem mem * m0_REG RName_0 (validate_seqh r0 mem) *
            m0_REG RName_3 (w2w (mem r0)))


*)
end
