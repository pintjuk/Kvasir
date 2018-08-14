loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/step"::(!loadPath));

open m0_stepLib
     val () = print_instructions () 
     val ev = thumb_step (true, true)  
     val ev_code = thumb_step_code (true, true)
     ev_code `bx lr`
(*
 output
     [[
[s.AIRCR.ENDIANNESS, s.CONTROL.SPSEL, s.CurrentMode ≠ Mode_Handler,
 14w ≠ 15w, s.MEM (s.REG RName_PC) = v2w [F; T; F; F; F; T; T; T],
 s.MEM (s.REG RName_PC + 1w) = v2w [F; T; T; T; F; F; F; F],
 s.exception = NoException, aligned 1 (s.REG RName_PC),
 word_bit 0 (s.REG (R_name T 14w))]
⊢ NextStateM0 s =
  SOME
    (s with
     <|REG :=
         (RName_PC =+ (31 >< 1) (s.REG (R_name T 14w)) @@ 0w) s.REG;
       count := s.count + 3; pcinc := 2w|>)]]: *)

     ev "ADD (pc)"
     ev "BX"
     
     m0_progTheory.M0_IMP_SPEC
