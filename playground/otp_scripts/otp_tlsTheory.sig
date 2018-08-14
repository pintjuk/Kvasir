signature otp_tlsTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val buffer_def : thm
    val encrypt_buffer_def : thm
    val encrypt_def : thm
    val get_seq_no_def : thm
    val max_seq_def : thm
    val otp_state_Buffer : thm
    val otp_state_Buffer_fupd : thm
    val otp_state_CurrSeq : thm
    val otp_state_CurrSeq_fupd : thm
    val otp_state_In : thm
    val otp_state_In_fupd : thm
    val otp_state_Key : thm
    val otp_state_Key_fupd : thm
    val otp_state_Out : thm
    val otp_state_Out_fupd : thm
    val otp_state_TY_DEF : thm
    val otp_state_case_def : thm
    val otp_state_size_def : thm
    val put_val_in_buf_def : thm
    val seq_in_order_def : thm
    val shift_buffer_def : thm
    val test_buffer_def : thm
    val tls_otp_spec_def : thm
    val uart_read_def : thm
    val uart_write_buffer_def : thm
    val valid_def : thm
    val zero_datah_def : thm

  (*  Theorems  *)
    val EXISTS_otp_state : thm
    val FORALL_otp_state : thm
    val datatype_otp_state : thm
    val otp_state_11 : thm
    val otp_state_Axiom : thm
    val otp_state_accessors : thm
    val otp_state_accfupds : thm
    val otp_state_case_cong : thm
    val otp_state_component_equality : thm
    val otp_state_fn_updates : thm
    val otp_state_fupdcanon : thm
    val otp_state_fupdcanon_comp : thm
    val otp_state_fupdfupds : thm
    val otp_state_fupdfupds_comp : thm
    val otp_state_induction : thm
    val otp_state_literal_11 : thm
    val otp_state_literal_nchotomy : thm
    val otp_state_nchotomy : thm
    val otp_state_updates_eq_literal : thm

  val otp_tls_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [words] Parent theory of "otp_tls"

   [buffer_def]  Definition

      |- ∀n.
           buffer n =
           case n of
             0 => 0w
           | 1 => 0w
           | 2 => 0w
           | 3 => 0w
           | 4 => 0w
           | 5 => 0w
           | 6 => 0w
           | 7 => 0w
           | 8 => 0w
           | 9 => 0w
           | v => ARB

   [encrypt_buffer_def]  Definition

      |- ∀f key seq.
           encrypt_buffer f key seq =
           (2 =+ encrypt (f 2) (key (8 * seq)))
             ((3 =+ encrypt (f 3) (key (8 * seq + 1)))
                ((4 =+ encrypt (f 4) (key (8 * seq + 2)))
                   ((5 =+ encrypt (f 5) (key (8 * seq + 3)))
                      ((6 =+ encrypt (f 6) (key (8 * seq + 4)))
                         ((7 =+ encrypt (f 7) (key (8 * seq + 5)))
                            ((8 =+ encrypt (f 8) (key (8 * seq + 6)))
                               ((9 =+ encrypt (f 9) (key (8 * seq + 7)))
                                  f)))))))

   [encrypt_def]  Definition

      |- ∀v k. encrypt v k = v ⊕ k

   [get_seq_no_def]  Definition

      |- ∀buf.
           get_seq_no buf =
           (let a = bit_field_insert 13 7 (buf 0) 0w
            in
              w2n (bit_field_insert 6 0 (buf 1) a))

   [max_seq_def]  Definition

      |- max_seq = 16383

   [otp_state_Buffer]  Definition

      |- ∀f n l l0 f0. (otp_state f n l l0 f0).Buffer = f

   [otp_state_Buffer_fupd]  Definition

      |- ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with Buffer updated_by f1 =
           otp_state (f1 f) n l l0 f0

   [otp_state_CurrSeq]  Definition

      |- ∀f n l l0 f0. (otp_state f n l l0 f0).CurrSeq = n

   [otp_state_CurrSeq_fupd]  Definition

      |- ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with CurrSeq updated_by f1 =
           otp_state f (f1 n) l l0 f0

   [otp_state_In]  Definition

      |- ∀f n l l0 f0. (otp_state f n l l0 f0).In = l

   [otp_state_In_fupd]  Definition

      |- ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with In updated_by f1 =
           otp_state f n (f1 l) l0 f0

   [otp_state_Key]  Definition

      |- ∀f n l l0 f0. (otp_state f n l l0 f0).Key = f0

   [otp_state_Key_fupd]  Definition

      |- ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with Key updated_by f1 =
           otp_state f n l l0 (f1 f0)

   [otp_state_Out]  Definition

      |- ∀f n l l0 f0. (otp_state f n l l0 f0).Out = l0

   [otp_state_Out_fupd]  Definition

      |- ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with Out updated_by f1 =
           otp_state f n l (f1 l0) f0

   [otp_state_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'otp_state' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4.
                        a0' =
                        (λa0 a1 a2 a3 a4.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4) ⇒
                     'otp_state' a0') ⇒
                  'otp_state' a0') rep

   [otp_state_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 f.
           otp_state_CASE (otp_state a0 a1 a2 a3 a4) f = f a0 a1 a2 a3 a4

   [otp_state_size_def]  Definition

      |- ∀a0 a1 a2 a3 a4.
           otp_state_size (otp_state a0 a1 a2 a3 a4) =
           1 + (a1 + (list_size (λv. 0) a2 + list_size (λv. 0) a3))

   [put_val_in_buf_def]  Definition

      |- ∀f b. put_val_in_buf f b = (9 =+ b) f

   [seq_in_order_def]  Definition

      |- ∀curr new. seq_in_order curr new ⇔ curr < new ∧ curr < max_seq

   [shift_buffer_def]  Definition

      |- ∀f.
           shift_buffer f =
           (0 =+ f 1)
             ((1 =+ f 2)
                ((2 =+ f 3)
                   ((3 =+ f 4)
                      ((4 =+ f 5)
                         ((5 =+ f 6)
                            ((6 =+ f 7)
                               ((7 =+ f 8)
                                  ((8 =+ f 9) ((9 =+ 0w) f)))))))))

   [test_buffer_def]  Definition

      |- test_buffer = (0 =+ 255w) ((1 =+ 255w) buffer)

   [tls_otp_spec_def]  Definition

      |- ∀s.
           tls_otp_spec s =
           (let s' =
                  s with
                  <|Buffer :=
                      put_val_in_buf (shift_buffer s.Buffer)
                        (uart_read s.In); In := TL s.In|>
            in
              if valid s'.Buffer then
                (let seq_no = get_seq_no s'.Buffer
                 in
                   if seq_in_order s'.CurrSeq seq_no then
                     (let newBuf =
                            zero_datah
                              (encrypt_buffer s'.Buffer s'.Key seq_no)
                      in
                      let newOut = uart_write_buffer s'.Out newBuf
                      in
                        s' with
                        <|Buffer := newBuf; CurrSeq := seq_no;
                          Out := newOut|>)
                   else s')
              else s')

   [uart_read_def]  Definition

      |- (uart_read [] = ARB) ∧ ∀x xs. uart_read (x::xs) = x

   [uart_write_buffer_def]  Definition

      |- ∀out buf.
           uart_write_buffer out buf =
           out ++
           [buf 0; buf 1; buf 2; buf 3; buf 4; buf 5; buf 6; buf 7; buf 8;
            buf 9]

   [valid_def]  Definition

      |- ∀buf.
           valid buf ⇔
           (word_msb (buf 0) ⇔ T) ∧ (word_msb (buf 1) ⇔ T) ∧
           (word_msb (buf 2) ⇔ F) ∧ (word_msb (buf 3) ⇔ F) ∧
           (word_msb (buf 4) ⇔ F) ∧ (word_msb (buf 5) ⇔ F) ∧
           (word_msb (buf 6) ⇔ F) ∧ (word_msb (buf 7) ⇔ F) ∧
           (word_msb (buf 8) ⇔ F) ∧ (word_msb (buf 9) ⇔ F)

   [zero_datah_def]  Definition

      |- ∀f.
           zero_datah f =
           (2 =+ f 2 && 127w)
             ((3 =+ f 3 && 127w)
                ((4 =+ f 4 && 127w)
                   ((5 =+ f 5 && 127w)
                      ((6 =+ f 6 && 127w)
                         ((7 =+ f 7 && 127w)
                            ((8 =+ f 8 && 127w)
                               ((9 =+ f 9 && 127w) f)))))))

   [EXISTS_otp_state]  Theorem

      |- ∀P.
           (∃ $o. P $o) ⇔
           ∃f0 n l0 l f.
             P <|Buffer := f0; CurrSeq := n; In := l0; Out := l; Key := f|>

   [FORALL_otp_state]  Theorem

      |- ∀P.
           (∀ $o. P $o) ⇔
           ∀f0 n l0 l f.
             P <|Buffer := f0; CurrSeq := n; In := l0; Out := l; Key := f|>

   [datatype_otp_state]  Theorem

      |- DATATYPE (record otp_state Buffer CurrSeq In Out Key)

   [otp_state_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a0' a1' a2' a3' a4'.
           (otp_state a0 a1 a2 a3 a4 = otp_state a0' a1' a2' a3' a4') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4')

   [otp_state_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4.
               fn (otp_state a0 a1 a2 a3 a4) = f a0 a1 a2 a3 a4

   [otp_state_accessors]  Theorem

      |- (∀f n l l0 f0. (otp_state f n l l0 f0).Buffer = f) ∧
         (∀f n l l0 f0. (otp_state f n l l0 f0).CurrSeq = n) ∧
         (∀f n l l0 f0. (otp_state f n l l0 f0).In = l) ∧
         (∀f n l l0 f0. (otp_state f n l l0 f0).Out = l0) ∧
         ∀f n l l0 f0. (otp_state f n l l0 f0).Key = f0

   [otp_state_accfupds]  Theorem

      |- (∀ $o f. ($o with CurrSeq updated_by f).Buffer = $o.Buffer) ∧
         (∀ $o f. ($o with In updated_by f).Buffer = $o.Buffer) ∧
         (∀ $o f. ($o with Out updated_by f).Buffer = $o.Buffer) ∧
         (∀ $o f. ($o with Key updated_by f).Buffer = $o.Buffer) ∧
         (∀ $o f. ($o with Buffer updated_by f).CurrSeq = $o.CurrSeq) ∧
         (∀ $o f. ($o with In updated_by f).CurrSeq = $o.CurrSeq) ∧
         (∀ $o f. ($o with Out updated_by f).CurrSeq = $o.CurrSeq) ∧
         (∀ $o f. ($o with Key updated_by f).CurrSeq = $o.CurrSeq) ∧
         (∀ $o f. ($o with Buffer updated_by f).In = $o.In) ∧
         (∀ $o f. ($o with CurrSeq updated_by f).In = $o.In) ∧
         (∀ $o f. ($o with Out updated_by f).In = $o.In) ∧
         (∀ $o f. ($o with Key updated_by f).In = $o.In) ∧
         (∀ $o f. ($o with Buffer updated_by f).Out = $o.Out) ∧
         (∀ $o f. ($o with CurrSeq updated_by f).Out = $o.Out) ∧
         (∀ $o f. ($o with In updated_by f).Out = $o.Out) ∧
         (∀ $o f. ($o with Key updated_by f).Out = $o.Out) ∧
         (∀ $o f. ($o with Buffer updated_by f).Key = $o.Key) ∧
         (∀ $o f. ($o with CurrSeq updated_by f).Key = $o.Key) ∧
         (∀ $o f. ($o with In updated_by f).Key = $o.Key) ∧
         (∀ $o f. ($o with Out updated_by f).Key = $o.Key) ∧
         (∀ $o f. ($o with Buffer updated_by f).Buffer = f $o.Buffer) ∧
         (∀ $o f. ($o with CurrSeq updated_by f).CurrSeq = f $o.CurrSeq) ∧
         (∀ $o f. ($o with In updated_by f).In = f $o.In) ∧
         (∀ $o f. ($o with Out updated_by f).Out = f $o.Out) ∧
         ∀ $o f. ($o with Key updated_by f).Key = f $o.Key

   [otp_state_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4.
              (M' = otp_state a0 a1 a2 a3 a4) ⇒
              (f a0 a1 a2 a3 a4 = f' a0 a1 a2 a3 a4)) ⇒
           (otp_state_CASE M f = otp_state_CASE M' f')

   [otp_state_component_equality]  Theorem

      |- ∀o1 o2.
           (o1 = o2) ⇔
           (o1.Buffer = o2.Buffer) ∧ (o1.CurrSeq = o2.CurrSeq) ∧
           (o1.In = o2.In) ∧ (o1.Out = o2.Out) ∧ (o1.Key = o2.Key)

   [otp_state_fn_updates]  Theorem

      |- (∀f1 f n l l0 f0.
            otp_state f n l l0 f0 with Buffer updated_by f1 =
            otp_state (f1 f) n l l0 f0) ∧
         (∀f1 f n l l0 f0.
            otp_state f n l l0 f0 with CurrSeq updated_by f1 =
            otp_state f (f1 n) l l0 f0) ∧
         (∀f1 f n l l0 f0.
            otp_state f n l l0 f0 with In updated_by f1 =
            otp_state f n (f1 l) l0 f0) ∧
         (∀f1 f n l l0 f0.
            otp_state f n l l0 f0 with Out updated_by f1 =
            otp_state f n l (f1 l0) f0) ∧
         ∀f1 f n l l0 f0.
           otp_state f n l l0 f0 with Key updated_by f1 =
           otp_state f n l l0 (f1 f0)

   [otp_state_fupdcanon]  Theorem

      |- (∀ $o g f.
            $o with <|CurrSeq updated_by f; Buffer updated_by g|> =
            $o with <|Buffer updated_by g; CurrSeq updated_by f|>) ∧
         (∀ $o g f.
            $o with <|In updated_by f; Buffer updated_by g|> =
            $o with <|Buffer updated_by g; In updated_by f|>) ∧
         (∀ $o g f.
            $o with <|In updated_by f; CurrSeq updated_by g|> =
            $o with <|CurrSeq updated_by g; In updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Out updated_by f; Buffer updated_by g|> =
            $o with <|Buffer updated_by g; Out updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Out updated_by f; CurrSeq updated_by g|> =
            $o with <|CurrSeq updated_by g; Out updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Out updated_by f; In updated_by g|> =
            $o with <|In updated_by g; Out updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Key updated_by f; Buffer updated_by g|> =
            $o with <|Buffer updated_by g; Key updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Key updated_by f; CurrSeq updated_by g|> =
            $o with <|CurrSeq updated_by g; Key updated_by f|>) ∧
         (∀ $o g f.
            $o with <|Key updated_by f; In updated_by g|> =
            $o with <|In updated_by g; Key updated_by f|>) ∧
         ∀ $o g f.
           $o with <|Key updated_by f; Out updated_by g|> =
           $o with <|Out updated_by g; Key updated_by f|>

   [otp_state_fupdcanon_comp]  Theorem

      |- ((∀g f.
             CurrSeq_fupd f ∘ Buffer_fupd g =
             Buffer_fupd g ∘ CurrSeq_fupd f) ∧
          ∀h g f.
            CurrSeq_fupd f ∘ Buffer_fupd g ∘ h =
            Buffer_fupd g ∘ CurrSeq_fupd f ∘ h) ∧
         ((∀g f. In_fupd f ∘ Buffer_fupd g = Buffer_fupd g ∘ In_fupd f) ∧
          ∀h g f.
            In_fupd f ∘ Buffer_fupd g ∘ h =
            Buffer_fupd g ∘ In_fupd f ∘ h) ∧
         ((∀g f. In_fupd f ∘ CurrSeq_fupd g = CurrSeq_fupd g ∘ In_fupd f) ∧
          ∀h g f.
            In_fupd f ∘ CurrSeq_fupd g ∘ h =
            CurrSeq_fupd g ∘ In_fupd f ∘ h) ∧
         ((∀g f. Out_fupd f ∘ Buffer_fupd g = Buffer_fupd g ∘ Out_fupd f) ∧
          ∀h g f.
            Out_fupd f ∘ Buffer_fupd g ∘ h =
            Buffer_fupd g ∘ Out_fupd f ∘ h) ∧
         ((∀g f.
             Out_fupd f ∘ CurrSeq_fupd g = CurrSeq_fupd g ∘ Out_fupd f) ∧
          ∀h g f.
            Out_fupd f ∘ CurrSeq_fupd g ∘ h =
            CurrSeq_fupd g ∘ Out_fupd f ∘ h) ∧
         ((∀g f. Out_fupd f ∘ In_fupd g = In_fupd g ∘ Out_fupd f) ∧
          ∀h g f.
            Out_fupd f ∘ In_fupd g ∘ h = In_fupd g ∘ Out_fupd f ∘ h) ∧
         ((∀g f. Key_fupd f ∘ Buffer_fupd g = Buffer_fupd g ∘ Key_fupd f) ∧
          ∀h g f.
            Key_fupd f ∘ Buffer_fupd g ∘ h =
            Buffer_fupd g ∘ Key_fupd f ∘ h) ∧
         ((∀g f.
             Key_fupd f ∘ CurrSeq_fupd g = CurrSeq_fupd g ∘ Key_fupd f) ∧
          ∀h g f.
            Key_fupd f ∘ CurrSeq_fupd g ∘ h =
            CurrSeq_fupd g ∘ Key_fupd f ∘ h) ∧
         ((∀g f. Key_fupd f ∘ In_fupd g = In_fupd g ∘ Key_fupd f) ∧
          ∀h g f.
            Key_fupd f ∘ In_fupd g ∘ h = In_fupd g ∘ Key_fupd f ∘ h) ∧
         (∀g f. Key_fupd f ∘ Out_fupd g = Out_fupd g ∘ Key_fupd f) ∧
         ∀h g f. Key_fupd f ∘ Out_fupd g ∘ h = Out_fupd g ∘ Key_fupd f ∘ h

   [otp_state_fupdfupds]  Theorem

      |- (∀ $o g f.
            $o with <|Buffer updated_by f; Buffer updated_by g|> =
            $o with Buffer updated_by f ∘ g) ∧
         (∀ $o g f.
            $o with <|CurrSeq updated_by f; CurrSeq updated_by g|> =
            $o with CurrSeq updated_by f ∘ g) ∧
         (∀ $o g f.
            $o with <|In updated_by f; In updated_by g|> =
            $o with In updated_by f ∘ g) ∧
         (∀ $o g f.
            $o with <|Out updated_by f; Out updated_by g|> =
            $o with Out updated_by f ∘ g) ∧
         ∀ $o g f.
           $o with <|Key updated_by f; Key updated_by g|> =
           $o with Key updated_by f ∘ g

   [otp_state_fupdfupds_comp]  Theorem

      |- ((∀g f. Buffer_fupd f ∘ Buffer_fupd g = Buffer_fupd (f ∘ g)) ∧
          ∀h g f.
            Buffer_fupd f ∘ Buffer_fupd g ∘ h = Buffer_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. CurrSeq_fupd f ∘ CurrSeq_fupd g = CurrSeq_fupd (f ∘ g)) ∧
          ∀h g f.
            CurrSeq_fupd f ∘ CurrSeq_fupd g ∘ h =
            CurrSeq_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. In_fupd f ∘ In_fupd g = In_fupd (f ∘ g)) ∧
          ∀h g f. In_fupd f ∘ In_fupd g ∘ h = In_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. Out_fupd f ∘ Out_fupd g = Out_fupd (f ∘ g)) ∧
          ∀h g f. Out_fupd f ∘ Out_fupd g ∘ h = Out_fupd (f ∘ g) ∘ h) ∧
         (∀g f. Key_fupd f ∘ Key_fupd g = Key_fupd (f ∘ g)) ∧
         ∀h g f. Key_fupd f ∘ Key_fupd g ∘ h = Key_fupd (f ∘ g) ∘ h

   [otp_state_induction]  Theorem

      |- ∀P. (∀f n l l0 f0. P (otp_state f n l l0 f0)) ⇒ ∀ $o. P $o

   [otp_state_literal_11]  Theorem

      |- ∀f01 n1 l01 l1 f1 f02 n2 l02 l2 f2.
           (<|Buffer := f01; CurrSeq := n1; In := l01; Out := l1;
              Key := f1|> =
            <|Buffer := f02; CurrSeq := n2; In := l02; Out := l2;
              Key := f2|>) ⇔
           (f01 = f02) ∧ (n1 = n2) ∧ (l01 = l02) ∧ (l1 = l2) ∧ (f1 = f2)

   [otp_state_literal_nchotomy]  Theorem

      |- ∀ $o.
           ∃f0 n l0 l f.
             $o =
             <|Buffer := f0; CurrSeq := n; In := l0; Out := l; Key := f|>

   [otp_state_nchotomy]  Theorem

      |- ∀oo. ∃f n l l0 f0. oo = otp_state f n l l0 f0

   [otp_state_updates_eq_literal]  Theorem

      |- ∀ $o f0 n l0 l f.
           $o with
           <|Buffer := f0; CurrSeq := n; In := l0; Out := l; Key := f|> =
           <|Buffer := f0; CurrSeq := n; In := l0; Out := l; Key := f|>


*)
end
