structure m0u_progTheory :> m0u_progTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading m0u_progTheory ... "
    else ()
  
  open Type Term Thm
  local open clockTheory uartTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "m0u_prog"
        (holpathdb.subst_pathvars "/home/daniil/Documents/Exjob/Kvasir/playground/uart_model/m0u_progTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op m0u_component_TY_DEF _ = ()
  val op m0u_component_TY_DEF = TDB.find "m0u_component_TY_DEF"
  fun op m0u_component_case_def _ = ()
  val op m0u_component_case_def = TDB.find "m0u_component_case_def"
  fun op m0u_component_size_def _ = ()
  val op m0u_component_size_def = TDB.find "m0u_component_size_def"
  fun op m0u_data_TY_DEF _ = ()
  val op m0u_data_TY_DEF = TDB.find "m0u_data_TY_DEF"
  fun op m0u_data_case_def _ = ()
  val op m0u_data_case_def = TDB.find "m0u_data_case_def"
  fun op m0u_data_size_def _ = ()
  val op m0u_data_size_def = TDB.find "m0u_data_size_def"
  fun op m0u_proj_def _ = () val op m0u_proj_def = TDB.find "m0u_proj_def"
  fun op TO_M0U_def _ = () val op TO_M0U_def = TDB.find "TO_M0U_def"
  fun op TO_M0U_PROP_def _ = ()
  val op TO_M0U_PROP_def = TDB.find "TO_M0U_PROP_def"
  fun op r2m0_c_set_def _ = ()
  val op r2m0_c_set_def = TDB.find "r2m0_c_set_def"
  fun op SDOM_def _ = () val op SDOM_def = TDB.find "SDOM_def"
  fun op NextStateM0U_def _ = ()
  val op NextStateM0U_def = TDB.find "NextStateM0U_def"
  fun op M0U_MODEL_def _ = ()
  val op M0U_MODEL_def = TDB.find "M0U_MODEL_def"
  fun op COSIM_def _ = () val op COSIM_def = TDB.find "COSIM_def"
  fun op datatype_m0u_component _ = ()
  val op datatype_m0u_component = TDB.find "datatype_m0u_component"
  fun op m0u_component_11 _ = ()
  val op m0u_component_11 = TDB.find "m0u_component_11"
  fun op m0u_component_distinct _ = ()
  val op m0u_component_distinct = TDB.find "m0u_component_distinct"
  fun op m0u_component_nchotomy _ = ()
  val op m0u_component_nchotomy = TDB.find "m0u_component_nchotomy"
  fun op m0u_component_Axiom _ = ()
  val op m0u_component_Axiom = TDB.find "m0u_component_Axiom"
  fun op m0u_component_induction _ = ()
  val op m0u_component_induction = TDB.find "m0u_component_induction"
  fun op m0u_component_case_cong _ = ()
  val op m0u_component_case_cong = TDB.find "m0u_component_case_cong"
  fun op m0u_component_case_eq _ = ()
  val op m0u_component_case_eq = TDB.find "m0u_component_case_eq"
  fun op datatype_m0u_data _ = ()
  val op datatype_m0u_data = TDB.find "datatype_m0u_data"
  fun op m0u_data_11 _ = () val op m0u_data_11 = TDB.find "m0u_data_11"
  fun op m0u_data_distinct _ = ()
  val op m0u_data_distinct = TDB.find "m0u_data_distinct"
  fun op m0u_data_nchotomy _ = ()
  val op m0u_data_nchotomy = TDB.find "m0u_data_nchotomy"
  fun op m0u_data_Axiom _ = ()
  val op m0u_data_Axiom = TDB.find "m0u_data_Axiom"
  fun op m0u_data_induction _ = ()
  val op m0u_data_induction = TDB.find "m0u_data_induction"
  fun op m0u_data_case_cong _ = ()
  val op m0u_data_case_cong = TDB.find "m0u_data_case_cong"
  fun op m0u_data_case_eq _ = ()
  val op m0u_data_case_eq = TDB.find "m0u_data_case_eq"
  fun op NEX_thm _ = () val op NEX_thm = TDB.find "NEX_thm"
  fun op NIT_NIT_STEP_thm _ = ()
  val op NIT_NIT_STEP_thm = TDB.find "NIT_NIT_STEP_thm"
  fun op NIT_COSIM_thm _ = ()
  val op NIT_COSIM_thm = TDB.find "NIT_COSIM_thm"
  fun op TP_def _ = () val op TP_def = TDB.find "TP_def"
  fun op WS_COSIM_thm _ = () val op WS_COSIM_thm = TDB.find "WS_COSIM_thm"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val m0u_prog_grammars = merge_grammars ["uart", "clock"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="m0u_prog"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val m0u_prog_grammars = 
    Portable.## (addtyUDs,addtmUDs) m0u_prog_grammars
  val _ = Parse.grammarDB_insert("m0u_prog",m0u_prog_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "m0u_prog"

end
