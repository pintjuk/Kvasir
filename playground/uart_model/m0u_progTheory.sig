signature m0u_progTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val COSIM_def : thm
    val DOM_def : thm
    val M0U_MODEL_def : thm
    val NextStateM0U_def : thm
    val TO_M0U_PROP_def : thm
    val TO_M0U_def : thm
    val UART_def : thm
    val cosim_def : thm
    val m0u_component_TY_DEF : thm
    val m0u_component_case_def : thm
    val m0u_component_size_def : thm
    val m0u_data_TY_DEF : thm
    val m0u_data_case_def : thm
    val m0u_data_size_def : thm
    val m0u_instr_primitive_def : thm
    val m0u_proj_def : thm
    val r2m0_c_set_def : thm
  
  (*  Theorems  *)
    val CODE_POOL_2_m0u_thm : thm
    val NEX_thm : thm
    val NIT_COSIM_thm : thm
    val cond_2_m0u_thm : thm
    val datatype_m0u_component : thm
    val datatype_m0u_data : thm
    val instr_2_m0u_thm : thm
    val m0_SDOM_STAR_thm : thm
    val m0u_component_11 : thm
    val m0u_component_Axiom : thm
    val m0u_component_case_cong : thm
    val m0u_component_case_eq : thm
    val m0u_component_distinct : thm
    val m0u_component_induction : thm
    val m0u_component_nchotomy : thm
    val m0u_data_11 : thm
    val m0u_data_Axiom : thm
    val m0u_data_case_cong : thm
    val m0u_data_case_eq : thm
    val m0u_data_distinct : thm
    val m0u_data_induction : thm
    val m0u_data_nchotomy : thm
    val m0u_instr_def : thm
    val m0u_instr_ind : thm
    val star_2_m0u_thm : thm
  
  val m0u_prog_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [clock] Parent theory of "m0u_prog"
   
   [m0_decomp] Parent theory of "m0u_prog"
   
   [uart] Parent theory of "m0u_prog"
   
   [COSIM_def]  Definition
      
       []
      ⊢ ∀P t.
            COSIM P t ⇔
            ∀s s' seq seq' i.
                SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s ∧
                rel_sequence (NEXT_REL $= NextStateM0) seq s ∧
                rel_sequence (NEXT_REL $= NextStateM0U) seq' s' ∧
                m0u_m0_non_r_eq uart_r s' s ∧ (seq i).count < s.count + t ⇒
                m0u_m0_non_r_eq uart_r (m0u_Next (seq' i)) (Next (seq i)) ∧
                m0u_r_eq uart_r (seq' i) (m0u_Next (seq' i))
   
   [DOM_def]  Definition
      
       [] ⊢ ∀A. DOM A = BIGUNION (IMAGE (IMAGE FST) A)
   
   [M0U_MODEL_def]  Definition
      
       []
      ⊢ M0U_MODEL =
        (STATE m0u_proj,NEXT_REL $= NextStateM0U,m0u_instr,$=,K F)
   
   [NextStateM0U_def]  Definition
      
       []
      ⊢ ∀s0.
            NextStateM0U s0 =
            (let
               s1 = m0u_Next s0
             in
               if ((FST ∘ FST) s1).exception = NoException then SOME s1
               else NONE)
   
   [TO_M0U_PROP_def]  Definition
      
       [] ⊢ TO_M0U_PROP = IMAGE TO_M0U
   
   [TO_M0U_def]  Definition
      
       [] ⊢ TO_M0U = IMAGE (m0_c ## m0_d)
   
   [UART_def]  Definition
      
       [] ⊢ UART = r2m0_c_set uart_r
   
   [cosim_def]  Definition
      
       [] ⊢ ∀P c t. cosim P c t ⇔ COSIM (CODE_POOL m0_instr c * P) t
   
   [m0u_component_TY_DEF]  Definition
      
       []
      ⊢ ∃rep.
            TYPE_DEFINITION
              (λa0.
                   ∀'m0u_component' .
                       (∀a0.
                            (∃a.
                                 a0 =
                                 (λa.
                                      ind_type$CONSTR 0 a
                                        (λn. ind_type$BOTTOM)) a) ∨
                            (a0 =
                             ind_type$CONSTR (SUC 0) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (a0 =
                             ind_type$CONSTR (SUC (SUC 0)) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (a0 =
                             ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (a0 =
                             ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (a0 =
                             ind_type$CONSTR
                               (SUC (SUC (SUC (SUC (SUC 0))))) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (a0 =
                             ind_type$CONSTR
                               (SUC (SUC (SUC (SUC (SUC (SUC 0)))))) ARB
                               (λn. ind_type$BOTTOM)) ⇒
                            'm0u_component' a0) ⇒
                       'm0u_component' a0) rep
   
   [m0u_component_case_def]  Definition
      
       []
      ⊢ (∀a f v v1 v2 v3 v4 v5.
             m0u_component_CASE (m0_c a) f v v1 v2 v3 v4 v5 = f a) ∧
        (∀f v v1 v2 v3 v4 v5.
             m0u_component_CASE m0u_c_Input f v v1 v2 v3 v4 v5 = v) ∧
        (∀f v v1 v2 v3 v4 v5.
             m0u_component_CASE m0u_c_Output f v v1 v2 v3 v4 v5 = v1) ∧
        (∀f v v1 v2 v3 v4 v5.
             m0u_component_CASE m0u_c_RXD f v v1 v2 v3 v4 v5 = v2) ∧
        (∀f v v1 v2 v3 v4 v5.
             m0u_component_CASE m0u_c_TXD f v v1 v2 v3 v4 v5 = v3) ∧
        (∀f v v1 v2 v3 v4 v5.
             m0u_component_CASE m0u_c_RXDRDY f v v1 v2 v3 v4 v5 = v4) ∧
        ∀f v v1 v2 v3 v4 v5.
            m0u_component_CASE m0u_c_TXDRDY f v v1 v2 v3 v4 v5 = v5
   
   [m0u_component_size_def]  Definition
      
       []
      ⊢ (∀a. m0u_component_size (m0_c a) = 1 + m0_component_size a) ∧
        (m0u_component_size m0u_c_Input = 0) ∧
        (m0u_component_size m0u_c_Output = 0) ∧
        (m0u_component_size m0u_c_RXD = 0) ∧
        (m0u_component_size m0u_c_TXD = 0) ∧
        (m0u_component_size m0u_c_RXDRDY = 0) ∧
        (m0u_component_size m0u_c_TXDRDY = 0)
   
   [m0u_data_TY_DEF]  Definition
      
       []
      ⊢ ∃rep.
            TYPE_DEFINITION
              (λa0.
                   ∀'m0u_data' .
                       (∀a0.
                            (∃a.
                                 a0 =
                                 (λa.
                                      ind_type$CONSTR 0 (a,ARB,ARB,ARB)
                                        (λn. ind_type$BOTTOM)) a) ∨
                            (∃a.
                                 a0 =
                                 (λa.
                                      ind_type$CONSTR (SUC 0)
                                        (ARB,a,ARB,ARB)
                                        (λn. ind_type$BOTTOM)) a) ∨
                            (∃a.
                                 a0 =
                                 (λa.
                                      ind_type$CONSTR (SUC (SUC 0))
                                        (ARB,ARB,a,ARB)
                                        (λn. ind_type$BOTTOM)) a) ∨
                            (∃a.
                                 a0 =
                                 (λa.
                                      ind_type$CONSTR (SUC (SUC (SUC 0)))
                                        (ARB,ARB,ARB,a)
                                        (λn. ind_type$BOTTOM)) a) ⇒
                            'm0u_data' a0) ⇒
                       'm0u_data' a0) rep
   
   [m0u_data_case_def]  Definition
      
       []
      ⊢ (∀a f f1 f2 f3. m0u_data_CASE (m0_d a) f f1 f2 f3 = f a) ∧
        (∀a f f1 f2 f3. m0u_data_CASE (m0u_d_stream a) f f1 f2 f3 = f1 a) ∧
        (∀a f f1 f2 f3. m0u_data_CASE (m0u_d_word32 a) f f1 f2 f3 = f2 a) ∧
        ∀a f f1 f2 f3. m0u_data_CASE (m0u_d_bool a) f f1 f2 f3 = f3 a
   
   [m0u_data_size_def]  Definition
      
       []
      ⊢ (∀a. m0u_data_size (m0_d a) = 1 + m0_data_size a) ∧
        (∀a. m0u_data_size (m0u_d_stream a) = 1 + list_size (λv. 0) a) ∧
        (∀a. m0u_data_size (m0u_d_word32 a) = 1) ∧
        ∀a. m0u_data_size (m0u_d_bool a) = 1 + bool_size a
   
   [m0u_instr_primitive_def]  Definition
      
       []
      ⊢ m0u_instr =
        WFREC (@R'. WF R')
          (λm0u_instr a'.
               case a' of
                 (a,INL opc16) =>
                   I
                     {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((7 >< 0) opc16)));
                      (m0_c (m0_c_MEM (a + 1w)),
                       m0_d (m0_d_word8 ((15 >< 8) opc16)))}
               | (a,INR opc32) =>
                 I
                   {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((23 >< 16) opc32)));
                    (m0_c (m0_c_MEM (a + 1w)),
                     m0_d (m0_d_word8 ((31 >< 24) opc32)));
                    (m0_c (m0_c_MEM (a + 2w)),
                     m0_d (m0_d_word8 ((7 >< 0) opc32)));
                    (m0_c (m0_c_MEM (a + 3w)),
                     m0_d (m0_d_word8 ((15 >< 8) opc32)))})
   
   [m0u_proj_def]  Definition
      
       []
      ⊢ ∀s u input output.
            m0u_proj ((s,u),input,output) =
            (λa.
                 case a of
                   m0_c b => m0_d (m0_proj s b)
                 | m0u_c_Input => m0u_d_stream input
                 | m0u_c_Output => m0u_d_stream output
                 | m0u_c_RXD => m0u_d_word32 u.RXD
                 | m0u_c_TXD => m0u_d_word32 u.RXD
                 | m0u_c_RXDRDY => m0u_d_word32 u.RXD
                 | m0u_c_TXDRDY => m0u_d_word32 u.RXD)
   
   [r2m0_c_set_def]  Definition
      
       [] ⊢ ∀region. r2m0_c_set region = IMAGE m0_c_MEM region
   
   [CODE_POOL_2_m0u_thm]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀code.
            TO_M0U_PROP (CODE_POOL m0_instr code) =
            CODE_POOL m0u_instr code
   
   [NEX_thm]  Theorem
      
       []
      ⊢ ∀P t.
            NEX P t ⇒
            ∀s seq i.
                SEP_REFINE (P * SEP_T) $= (STATE m0_proj) s ∧
                rel_sequence (NEXT_REL $= NextStateM0) seq s ∧
                (seq i).count < s.count + t ⇒
                (seq i).count < (Next (seq i)).count ∧
                (Next (seq i) = seq (SUC i))
   
   [NIT_COSIM_thm]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀P t. NIT uart_r P t ∧ NEX P t ⇒ COSIM P t
   
   [cond_2_m0u_thm]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀x. TO_M0U_PROP (cond x) = cond x
   
   [datatype_m0u_component]  Theorem
      
       []
      ⊢ DATATYPE
          (m0u_component m0_c m0u_c_Input m0u_c_Output m0u_c_RXD m0u_c_TXD
             m0u_c_RXDRDY m0u_c_TXDRDY)
   
   [datatype_m0u_data]  Theorem
      
       [] ⊢ DATATYPE (m0u_data m0_d m0u_d_stream m0u_d_word32 m0u_d_bool)
   
   [instr_2_m0u_thm]  Theorem
      
       [] ⊢ TO_M0U ∘ m0_instr = m0u_instr
   
   [m0_SDOM_STAR_thm]  Theorem
      
       [] ⊢ ∀A B x. DOM (A * B) x ⇒ (DOM A ∪ DOM B) x
   
   [m0u_component_11]  Theorem
      
       [] ⊢ ∀a a'. (m0_c a = m0_c a') ⇔ (a = a')
   
   [m0u_component_Axiom]  Theorem
      
       []
      ⊢ ∀f0 f1 f2 f3 f4 f5 f6.
            ∃fn.
                (∀a. fn (m0_c a) = f0 a) ∧ (fn m0u_c_Input = f1) ∧
                (fn m0u_c_Output = f2) ∧ (fn m0u_c_RXD = f3) ∧
                (fn m0u_c_TXD = f4) ∧ (fn m0u_c_RXDRDY = f5) ∧
                (fn m0u_c_TXDRDY = f6)
   
   [m0u_component_case_cong]  Theorem
      
       []
      ⊢ ∀M M' f v v1 v2 v3 v4 v5.
            (M = M') ∧ (∀a. (M' = m0_c a) ⇒ (f a = f' a)) ∧
            ((M' = m0u_c_Input) ⇒ (v = v')) ∧
            ((M' = m0u_c_Output) ⇒ (v1 = v1')) ∧
            ((M' = m0u_c_RXD) ⇒ (v2 = v2')) ∧
            ((M' = m0u_c_TXD) ⇒ (v3 = v3')) ∧
            ((M' = m0u_c_RXDRDY) ⇒ (v4 = v4')) ∧
            ((M' = m0u_c_TXDRDY) ⇒ (v5 = v5')) ⇒
            (m0u_component_CASE M f v v1 v2 v3 v4 v5 =
             m0u_component_CASE M' f' v' v1' v2' v3' v4' v5')
   
   [m0u_component_case_eq]  Theorem
      
       []
      ⊢ (m0u_component_CASE x f v v1 v2 v3 v4 v5 = v') ⇔
        (∃m. (x = m0_c m) ∧ (f m = v')) ∨ (x = m0u_c_Input) ∧ (v = v') ∨
        (x = m0u_c_Output) ∧ (v1 = v') ∨ (x = m0u_c_RXD) ∧ (v2 = v') ∨
        (x = m0u_c_TXD) ∧ (v3 = v') ∨ (x = m0u_c_RXDRDY) ∧ (v4 = v') ∨
        (x = m0u_c_TXDRDY) ∧ (v5 = v')
   
   [m0u_component_distinct]  Theorem
      
       []
      ⊢ (∀a. m0_c a ≠ m0u_c_Input) ∧ (∀a. m0_c a ≠ m0u_c_Output) ∧
        (∀a. m0_c a ≠ m0u_c_RXD) ∧ (∀a. m0_c a ≠ m0u_c_TXD) ∧
        (∀a. m0_c a ≠ m0u_c_RXDRDY) ∧ (∀a. m0_c a ≠ m0u_c_TXDRDY) ∧
        m0u_c_Input ≠ m0u_c_Output ∧ m0u_c_Input ≠ m0u_c_RXD ∧
        m0u_c_Input ≠ m0u_c_TXD ∧ m0u_c_Input ≠ m0u_c_RXDRDY ∧
        m0u_c_Input ≠ m0u_c_TXDRDY ∧ m0u_c_Output ≠ m0u_c_RXD ∧
        m0u_c_Output ≠ m0u_c_TXD ∧ m0u_c_Output ≠ m0u_c_RXDRDY ∧
        m0u_c_Output ≠ m0u_c_TXDRDY ∧ m0u_c_RXD ≠ m0u_c_TXD ∧
        m0u_c_RXD ≠ m0u_c_RXDRDY ∧ m0u_c_RXD ≠ m0u_c_TXDRDY ∧
        m0u_c_TXD ≠ m0u_c_RXDRDY ∧ m0u_c_TXD ≠ m0u_c_TXDRDY ∧
        m0u_c_RXDRDY ≠ m0u_c_TXDRDY
   
   [m0u_component_induction]  Theorem
      
       []
      ⊢ ∀P.
            (∀m. P (m0_c m)) ∧ P m0u_c_Input ∧ P m0u_c_Output ∧
            P m0u_c_RXD ∧ P m0u_c_TXD ∧ P m0u_c_RXDRDY ∧ P m0u_c_TXDRDY ⇒
            ∀m. P m
   
   [m0u_component_nchotomy]  Theorem
      
       []
      ⊢ ∀mm.
            (∃m. mm = m0_c m) ∨ (mm = m0u_c_Input) ∨ (mm = m0u_c_Output) ∨
            (mm = m0u_c_RXD) ∨ (mm = m0u_c_TXD) ∨ (mm = m0u_c_RXDRDY) ∨
            (mm = m0u_c_TXDRDY)
   
   [m0u_data_11]  Theorem
      
       []
      ⊢ (∀a a'. (m0_d a = m0_d a') ⇔ (a = a')) ∧
        (∀a a'. (m0u_d_stream a = m0u_d_stream a') ⇔ (a = a')) ∧
        (∀a a'. (m0u_d_word32 a = m0u_d_word32 a') ⇔ (a = a')) ∧
        ∀a a'. (m0u_d_bool a = m0u_d_bool a') ⇔ (a ⇔ a')
   
   [m0u_data_Axiom]  Theorem
      
       []
      ⊢ ∀f0 f1 f2 f3.
            ∃fn.
                (∀a. fn (m0_d a) = f0 a) ∧
                (∀a. fn (m0u_d_stream a) = f1 a) ∧
                (∀a. fn (m0u_d_word32 a) = f2 a) ∧
                ∀a. fn (m0u_d_bool a) = f3 a
   
   [m0u_data_case_cong]  Theorem
      
       []
      ⊢ ∀M M' f f1 f2 f3.
            (M = M') ∧ (∀a. (M' = m0_d a) ⇒ (f a = f' a)) ∧
            (∀a. (M' = m0u_d_stream a) ⇒ (f1 a = f1' a)) ∧
            (∀a. (M' = m0u_d_word32 a) ⇒ (f2 a = f2' a)) ∧
            (∀a. (M' = m0u_d_bool a) ⇒ (f3 a = f3' a)) ⇒
            (m0u_data_CASE M f f1 f2 f3 = m0u_data_CASE M' f' f1' f2' f3')
   
   [m0u_data_case_eq]  Theorem
      
       []
      ⊢ (m0u_data_CASE x f f1 f2 f3 = v) ⇔
        (∃m. (x = m0_d m) ∧ (f m = v)) ∨
        (∃l. (x = m0u_d_stream l) ∧ (f1 l = v)) ∨
        (∃c. (x = m0u_d_word32 c) ∧ (f2 c = v)) ∨
        ∃b. (x = m0u_d_bool b) ∧ (f3 b = v)
   
   [m0u_data_distinct]  Theorem
      
       []
      ⊢ (∀a' a. m0_d a ≠ m0u_d_stream a') ∧
        (∀a' a. m0_d a ≠ m0u_d_word32 a') ∧
        (∀a' a. m0_d a ≠ m0u_d_bool a') ∧
        (∀a' a. m0u_d_stream a ≠ m0u_d_word32 a') ∧
        (∀a' a. m0u_d_stream a ≠ m0u_d_bool a') ∧
        ∀a' a. m0u_d_word32 a ≠ m0u_d_bool a'
   
   [m0u_data_induction]  Theorem
      
       []
      ⊢ ∀P.
            (∀m. P (m0_d m)) ∧ (∀l. P (m0u_d_stream l)) ∧
            (∀c. P (m0u_d_word32 c)) ∧ (∀b. P (m0u_d_bool b)) ⇒
            ∀m. P m
   
   [m0u_data_nchotomy]  Theorem
      
       []
      ⊢ ∀mm.
            (∃m. mm = m0_d m) ∨ (∃l. mm = m0u_d_stream l) ∨
            (∃c. mm = m0u_d_word32 c) ∨ ∃b. mm = m0u_d_bool b
   
   [m0u_instr_def]  Theorem
      
       []
      ⊢ (m0u_instr (a,INL opc16) =
         {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((7 >< 0) opc16)));
          (m0_c (m0_c_MEM (a + 1w)),m0_d (m0_d_word8 ((15 >< 8) opc16)))}) ∧
        (m0u_instr (a,INR opc32) =
         {(m0_c (m0_c_MEM a),m0_d (m0_d_word8 ((23 >< 16) opc32)));
          (m0_c (m0_c_MEM (a + 1w)),m0_d (m0_d_word8 ((31 >< 24) opc32)));
          (m0_c (m0_c_MEM (a + 2w)),m0_d (m0_d_word8 ((7 >< 0) opc32)));
          (m0_c (m0_c_MEM (a + 3w)),m0_d (m0_d_word8 ((15 >< 8) opc32)))})
   
   [m0u_instr_ind]  Theorem
      
       []
      ⊢ ∀P.
            (∀a opc16. P (a,INL opc16)) ∧ (∀a opc32. P (a,INR opc32)) ⇒
            ∀v v1. P (v,v1)
   
   [star_2_m0u_thm]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀a b. TO_M0U_PROP (a * b) = TO_M0U_PROP a * TO_M0U_PROP b
   
   
*)
end
