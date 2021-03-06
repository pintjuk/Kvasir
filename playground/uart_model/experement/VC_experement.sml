(*
    loadPath := ("/home/daniil/Apps/HOL/examples/l3-machine-code/m0/decompiler"::(!loadPath));
    loadPath := ("/Home/daniil/Apps/HOL/examples/l3-machine-code/common"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/helpers"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/nit2bisim"::(!loadPath));
    loadPath := ("/home/daniil/projects/Kvasir/playground/uart_model/prog"::(!loadPath));
*)
structure nit_prover = 
struct 

    open m0u_progTheory;
    open Int;
    open m0_decompLib;
    open m0Theory;
    open pairLib;
    open pred_setSyntax;
    open m0_progLib;
    open m0_stepLib;
    open wordsSyntax;
    open wordsSyntax
    open progSyntax;

    open sep_helper; 
    exception Unimpl;


    fun VC entry [(offset, inst)] =  ASSUME ``x:'a`` 
    | VC entry ((a, b)::t) = raise Unimpl
    | VC entry [] = raise Unimpl ;

    (* Conert instructions *)
    fun instrHex inst_th = (
        fmt StringCvt.HEX o 
        uint_of_word o 
        snd o
        dest_comb 
    ) inst_th;

    fun getCode x = (#3 o dest_spec o concl) x;
    fun termToTuple x = let
        val addrTerm2Int = fn x =>
                if is_word_add x
                then (uint_of_word o #2 o dest_word_add) x
                else 0
        val ontouple = fn (addr, code) => (addrTerm2Int addr, instrHex code)
    in (ontouple o dest_pair ) x end;
    fun codeThmToList x = ((map termToTuple ) o strip_set) x;

    fun getCodeFromThm x = (codeThmToList o getCode) x;

    (*
    (codeThmToList o getCode) code_th 
    *)

    (* Getting what we need *)


    fun getTimeFromSpec spec:term =
    let
        val specparts = ( dest_spec o concl) spec
        val stripstuff = (map dest_comb) o strip_star 
        val findCount = List.find (fn (x,y:term) => ``m0_count``=x )
        val get: (((term * term) option) -> term*term) = (
            fn opt => case  opt of                           
                    SOME value => value
                    |NONE => raise Fail "precondition and post conditon must have m0_count")
        val pre_count =  (#2 o get o findCount o stripstuff o #2 ) specparts 
        val post_count = (#2 o get o findCount o stripstuff o #4 ) specparts
    in (hd o tl o numSyntax.strip_plus) post_count end

    (*
    test getTimefro spec:

    val test = (hd  (m0_spec_hex "00C0"))
    getTimeFromSpec (hd  (m0_spec_hex "00C0"))
    *)

    (* next state theorem *) 

code_th code_defs

    val (code_th, code_defs) = m0_decompile "code"` 
    00c0   (* lsls r0, r0, #3      *)
    5c14   (* ldrb r4, [r2, r0]    *)
    788b   (* ldrb r3, [r1, #2]    *)
    1812   (* adds r2, r2, r0      *)
    4063   (* eors r3, r4          *)
    708b   (* strb r3, [r1, #2]    *)
    7850   (* ldrb r0, [r2, #1]    *)
    78cb   (* ldrb r3, [r1, #3]    *)
    4043   (* eors r3, r0          *)
    70cb   (* strb r3, [r1, #3]    *)
    7890   (* ldrb r0, [r2, #2]    *)
    790b   (* ldrb r3, [r1, #4]    *)
    4043   (* eors r3, r0          *)
    710b   (* strb r3, [r1, #4]    *)
    78d0   (* ldrb r0, [r2, #3]    *)
    794b   (* ldrb r3, [r1, #5]    *)
    4043   (* eors r3, r0          *)
    714b   (* strb r3, [r1, #5]    *)
    7910   (* ldrb r0, [r2, #4]    *)
    798b   (* ldrb r3, [r1, #6]    *)
    4043   (* eors r3, r0          *)
    718b   (* strb r3, [r1, #6]    *)
    7950   (* ldrb r0, [r2, #5]    *)
    79cb   (* ldrb r3, [r1, #7]    *)
    4043   (* eors r3, r0          *)
    71cb   (* strb r3, [r1, #7]    *)
    7990   (* ldrb r0, [r2, #6]    *)
    7a0b   (* ldrb r3, [r1, #8]    *)
    4043   (* eors r3, r0          *)
    720b   (* strb r3, [r1, #8]    *)
    79d2   (* ldrb r2, [r2, #7]    *)
    7a4b   (* ldrb r3, [r1, #9]    *)
    4053   (* eors r3, r2          *)
    724b   (* strb r3, [r1, #9]    *)
    `;

    val step_ev = thumb_step_hex (true, true);
    val codeList = getCodeFromThm code_th;
    val decoded = map (fn (x:int, y) => thumb_decode_hex false ( y)) codeList;
    val instr_specs = map (fn (x:int, y) => m0_spec_hex y) codeList;
    val instr_steps = map (fn (x:int, y) => step_ev y) codeList;


    val step =  (hd o hd) instr_steps
    val spec =  ((hd o hd) instr_specs) 
    val stepCount = getTimeFromSpec spec
    val runThm = REWRITE_RULE [progTheory.SPEC_def, M0_MODEL_def] spec
    val pre = ( rand o rator o concl) runThm
    val nexGOAL = mk_comb(mk_comb( ``NEX``, pre), stepCount)

    val nexTHMexp = (REWRITE_CONV [uartTheory.NEX_def]) nexGOAL


    ``∀s seq i count.
            SEP_REFINE
            (CODE_POOL m0_instr {(pc,INL 192w)} *
                (m0_count count * m0_PSR_N n * m0_PSR_Z z * m0_PSR_C c *
                m0_REG RName_0 r0 * m0_CONFIG (F,F) * m0_PC pc) * SEP_T) $=
            (STATE m0_proj) s ∧ rel_sequence (NEXT_REL $= NextStateM0) seq s ∧
            (seq (SUC i)).count ≤ s.count + 1 ⇒
            (seq i).count < (Next (seq i)).count ∧
            ((Next (seq i)).exception = NoException)``

    CONV_TAC SEP_CONV>>
    REPEAT GEN_TAC>>
    STRIP_TAC>>
    Cases_on `i` -<
    Q.PAT_X_ASSUM `_=pc` (  MP_TAC o GSYM  )
    strip_tac
    FULL_SIMP_TAC std_ss [progTheory.rel_sequence_def]

                        DB.find "rel_sequence"

    BBLAST_CONV ``s.MEM (s.REG RName_PC) = v2w [F; F; F; F; F; F; F; F]``

    Q.PAT_X_ASSUM `s.MEM _ = _` (MP_TAC o BBLAST_RULE )




    ``( (CODE_POOL m0_instr {(pc,INL 192w)}) *(m0_count count) )``

    val   code2_thm =  m0_spec_hex "f7ffffb9"
    ``0xffffw``

    open m0_progLib;
    get_code code_th

    map get_code (m0_spec "BL")

    m0_sp

    m0_spec_hex

    val inst = 
    thumb_decode_hex false inst


    case (( dest_comb o  snd o  dest_pair o  hd o strip_set o  #3 o  dest_spec o concl) code_th) of
        ("INL", inst) => uint_of_word inst 
    | ("INR", inst) => uint_of_word inst;



    dest_prod

    dist_pair inst


    val () = print_instructions () 

    val ev_code = thumb_step_code (true, true)
    ev_code `bx lr`
end
