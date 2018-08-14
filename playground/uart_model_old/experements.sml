        
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/model"::(!loadPath));
loadPath := ("/Home/daniil/HOL/examples/l3-machine-code/common"::(!loadPath));
loadPath := ("/home/daniil/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));
open  wordsTheory;
open m0Theory;
open m0_decompLib;
open fcpTheory;
     

EVAL ``(6w):word3``

val (daniil_th, daniil_defs) = m0_decompile "daniil_test" `
2300 (* movs r3, #0 *)`;

val (daniil_th, daniil_defs) = m0_decompile "daniil_test" `
f7ff ffe2 (* 	bl	17a <validate_seq_headers>*)`;


DB.find "daniil_test_pre";




uart_reg_load

uart_reg_store (state, dev) = 
DB.find "m0_REG"



(* test program *)
val q =
   `movs r1, #0              ; accumulator
    mov  r3, r0              ; first address
    adds r3, #40             ; last address (10 loads)
l1: ldr  r2, [r0, #4]        ; load data
    adds r0, #4              ; increment address
    add  r1, r2              ; add to accumulator
    cmp  r0, r3              ; test if done
    ble  l1                  ; loop if not done`


(* test program *)
val q =
   `l1: bl  l1                  ; loop if not done`


add_decompiled
derive_individual_specs
(* from GAS *)
val (test_cert, test_def) = m0_decompile "test" `
   2100
   0003
   3328
   6842
   3004
   4411
   4298
   DBFA`

get_decompiled "test"
 decompiler_memory

(* internal assembler *)
val () = m0AssemblerLib.print_m0_code `

m0_decompLib
 derive_individual_specs 
val (test2_cert, test2_def) = m0_decompile_code "test2" `
	mov	r3, #0  `		
	lslsne	r0, r0, #3 
`
val () = m0AssemblerLib.print_m0_code q

m0_decompLib
 derive_individual_specs 
val (test2_cert, test2_def) = m0_decompile_code "test2" q

val () = computeLib.add_funs [test_def]
val () = computeLib.add_funs [test2_def]

val run1 = Theory.save_thm("run1",
  EVAL ``test (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``)

val run2 = Theory.save_thm("run2",
  EVAL ``test2 (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``)

val () = export_theory()



(** remove this **)
open HolKernel Parse boolLib bossLib
open decompilerLib m0_progLib m0_progTheory m0_decompTheory


local
   fun get_length th =
      if sumSyntax.is_inl (m0_progLib.get_code th) then 2 else 4
   val find_exit =
      stateLib.get_pc_delta
          (Lib.equal "m0_prog$m0_PC" o fst o boolSyntax.dest_strip_comb)
   fun format_thm th = (th, get_length th, find_exit th)
   val count_INTRO_rule =
      stateLib.introduce_triple_definition (false, m0_COUNT_def) o
      Thm.INST [``endianness:bool`` |-> boolSyntax.F,
                ``spsel:bool`` |-> boolSyntax.F]
   val finalise =
      List.map format_thm o stateLib.fix_precond o List.map count_INTRO_rule
in
   val set_opt = m0_progLib.m0_config false
   fun m0_triples hex =
      case finalise (m0_progLib.m0_spec_hex hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "m0_triples" ""
   fun m0_triples_opt s hex = (set_opt s; m0_triples hex)
end

val m0_pc = Term.prim_mk_const {Thy = "m0_prog", Name = "m0_PC"}

fun m0_tools f hide = (f, fn _ => fail(), hide, m0_pc): decompiler_tools
fun m0_tools_opt opt = m0_tools (m0_triples_opt opt)

val l3_m0_tools = m0_tools m0_triples m0_NZCV_HIDE
val l3_m0_tools_no_status = m0_tools m0_triples TRUTH

val l3_m0_tools_flat = m0_tools_opt "flat" m0_NZCV_HIDE
val l3_m0_tools_array = m0_tools_opt "array" m0_NZCV_HIDE
val l3_m0_tools_mapped = m0_tools_opt "mapped" m0_NZCV_HIDE

val l3_m0_tools_flat_no_status = m0_tools_opt "flat" TRUTH
val l3_m0_tools_array_no_status = m0_tools_opt "array" TRUTH
val l3_m0_tools_mapped_no_status = m0_tools_opt "mapped" TRUTH

fun m0_decompile name qcode =
   (set_opt "mapped"; decompilerLib.decompile l3_m0_tools name qcode)

fun m0_decompile_code name (qass: string quotation) =
   ( set_opt "mapped"
   ; decompilerLib.decompile_with m0AssemblerLib.m0_code l3_m0_tools name qass
   )
