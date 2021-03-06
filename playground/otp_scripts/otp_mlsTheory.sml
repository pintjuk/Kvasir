structure otp_mlsTheory :> otp_mlsTheory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading otp_mlsTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (* Parents and ML dependencies *)
  local open m0_otp_decompTheory
  in end;
  val _ = Theory.link_parents
          ("otp_mls",
          Arbnum.fromString "1534163635",
          Arbnum.fromString "238992")
          [("m0_otp_decomp",
           Arbnum.fromString "1534161938",
           Arbnum.fromString "843438")];
  val _ = Theory.incorporate_types "otp_mls" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("fcp", "cart"), ID("min", "bool"),
   ID("fcp", "bit0"), ID("one", "one"), ID("pair", "prod"),
   ID("num", "num"), ID("bool", "!"), ID("arithmetic", "+"),
   ID("pair", ","), ID("sum", "sum"), ID("bool", "/\\"), ID("num", "0"),
   ID("min", "="), ID("arithmetic", "BIT1"), ID("arithmetic", "BIT2"),
   ID("pred_set", "EMPTY"), ID("sum", "INL"), ID("pred_set", "INSERT"),
   ID("m0_prog", "M0_MODEL"), ID("m0", "m0_state"),
   ID("m0_prog", "m0_data"), ID("m0_prog", "m0_component"),
   ID("arithmetic", "NUMERAL"), ID("m0", "RName_0"), ID("m0", "RName"),
   ID("m0", "RName_2"), ID("m0", "RName_3"), ID("set_sep", "SEP_HIDE"),
   ID("prog", "SPEC"), ID("set_sep", "STAR"), ID("pred_set", "SUBSET"),
   ID("combin", "UPDATE"), ID("arithmetic", "ZERO"),
   ID("otp_mls", "buffer"), ID("set_sep", "cond"),
   ID("otp_mls", "get_seq_no"), ID("m0_decomp", "m0_COUNT"),
   ID("m0_prog", "m0_MEMORY"), ID("m0_prog", "m0_NZCV"),
   ID("m0_prog", "m0_PC"), ID("m0_prog", "m0_REG"),
   ID("otp_mls", "mls_encrypt"), ID("otp_mls", "mls_shift_one"),
   ID("words", "n2w"), ID("otp_mls", "shift_buffer"),
   ID("otp_mls", "six_or"), ID("otp_mls", "validate_datah"),
   ID("otp_mls", "validate_seqh"), ID("words", "w2w"),
   ID("words", "word_1comp"), ID("words", "word_add"),
   ID("words", "word_and"), ID("words", "word_extract"),
   ID("words", "word_lsl"), ID("words", "word_lsr"),
   ID("words", "word_mul"), ID("words", "word_or"),
   ID("words", "word_xor"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'a", TYOP [2], TYOP [1, 1, 0], TYV "'c", TYOP [1, 1, 3], TYV "'b",
   TYOP [1, 1, 5], TYOP [0, 6, 4], TYOP [0, 7, 2], TYOP [0, 6, 8],
   TYOP [0, 6, 2], TYOP [0, 10, 2], TYOP [0, 6, 11], TYOP [4],
   TYOP [3, 13], TYOP [3, 14], TYOP [3, 15], TYOP [1, 1, 16], TYOP [3, 16],
   TYOP [3, 18], TYOP [1, 1, 19], TYOP [0, 20, 17], TYOP [0, 21, 21],
   TYOP [0, 20, 22], TYOP [0, 2, 6], TYOP [0, 24, 1], TYOP [0, 2, 25],
   TYOP [0, 20, 23], TYOP [0, 20, 27], TYOP [0, 21, 20], TYOP [0, 20, 29],
   TYOP [0, 20, 1], TYOP [5, 31, 21], TYOP [6], TYOP [5, 33, 32],
   TYOP [5, 20, 34], TYOP [0, 35, 1], TYOP [0, 2, 1], TYOP [0, 37, 1],
   TYOP [0, 6, 1], TYOP [0, 39, 1], TYOP [0, 31, 1], TYOP [0, 25, 1],
   TYOP [0, 10, 1], TYOP [0, 43, 1], TYOP [0, 7, 1], TYOP [0, 45, 1],
   TYOP [0, 41, 1], TYOP [0, 21, 1], TYOP [0, 48, 1], TYOP [0, 33, 1],
   TYOP [0, 50, 1], TYOP [0, 33, 33], TYOP [0, 33, 52], TYOP [0, 34, 35],
   TYOP [0, 20, 54], TYOP [1, 1, 18], TYOP [10, 56, 20], TYOP [5, 20, 57],
   TYOP [0, 57, 58], TYOP [0, 20, 59], TYOP [0, 21, 32], TYOP [0, 31, 61],
   TYOP [0, 32, 34], TYOP [0, 33, 63], TYOP [0, 1, 1], TYOP [0, 1, 65],
   TYOP [0, 2, 37], TYOP [0, 20, 31], TYOP [0, 24, 25], TYOP [0, 21, 48],
   TYOP [0, 58, 1], TYOP [0, 56, 57], TYOP [0, 31, 31], TYOP [0, 20, 73],
   TYOP [0, 71, 71], TYOP [0, 58, 75], TYOP [20], TYOP [0, 77, 1],
   TYOP [0, 77, 78], TYOP [5, 79, 78], TYOP [21], TYOP [22],
   TYOP [5, 82, 81], TYOP [0, 83, 1], TYOP [0, 58, 84], TYOP [5, 85, 80],
   TYOP [5, 79, 86], TYOP [0, 77, 84], TYOP [5, 88, 87], TYOP [25],
   TYOP [0, 84, 1], TYOP [0, 20, 91], TYOP [0, 92, 91], TYOP [5, 1, 1],
   TYOP [5, 1, 94], TYOP [5, 1, 95], TYOP [0, 96, 91], TYOP [0, 97, 91],
   TYOP [0, 91, 1], TYOP [0, 71, 99], TYOP [0, 91, 100], TYOP [0, 89, 101],
   TYOP [0, 91, 91], TYOP [0, 91, 103], TYOP [0, 31, 41], TYOP [0, 24, 24],
   TYOP [0, 6, 106], TYOP [0, 2, 107], TYOP [0, 17, 22], TYOP [0, 20, 109],
   TYOP [0, 1, 91], TYOP [0, 33, 91], TYOP [0, 21, 91], TYOP [0, 31, 113],
   TYOP [0, 90, 92], TYOP [0, 33, 2], TYOP [0, 33, 6], TYOP [0, 33, 20],
   TYOP [0, 33, 56], TYOP [0, 33, 17], TYOP [0, 7, 4], TYOP [0, 6, 121],
   TYOP [0, 4, 2], TYOP [0, 17, 20], TYOP [0, 2, 2], TYOP [0, 2, 125],
   TYOP [0, 6, 6], TYOP [0, 6, 127], TYOP [0, 20, 20], TYOP [0, 20, 129],
   TYOP [0, 4, 4], TYOP [0, 4, 131], TYOP [0, 33, 24], TYOP [0, 33, 133],
   TYOP [0, 20, 118], TYOP [0, 2, 116], TYOP [0, 17, 17],
   TYOP [0, 17, 137]]
  end
  val _ = Theory.incorporate_consts "otp_mls" tyvector
     [("validate_seqh", 9), ("validate_datah", 9), ("six_or", 12),
      ("shift_buffer", 23), ("mls_shift_one", 26), ("mls_encrypt", 28),
      ("get_seq_no", 30), ("buffer", 36)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("a", 2), TMV("a", 20), TMV("buf", 20), TMV("count", 33),
   TMV("dmem", 31), TMV("key", 20), TMV("m", 24), TMV("m", 10),
   TMV("m", 7), TMV("m", 21), TMV("mem", 21), TMV("p", 20), TMV("r0", 20),
   TMV("seq", 20), TMV("x", 6), TMV("x", 20), TMC(7, 38), TMC(7, 40),
   TMC(7, 41), TMC(7, 42), TMC(7, 44), TMC(7, 46), TMC(7, 47), TMC(7, 49),
   TMC(7, 51), TMC(8, 53), TMC(9, 55), TMC(9, 60), TMC(9, 62), TMC(9, 64),
   TMC(11, 66), TMC(12, 33), TMC(13, 66), TMC(13, 67), TMC(13, 68),
   TMC(13, 69), TMC(13, 70), TMC(14, 52), TMC(15, 52), TMC(16, 31),
   TMC(16, 71), TMC(17, 72), TMC(18, 74), TMC(18, 76), TMC(19, 89),
   TMC(23, 52), TMC(24, 90), TMC(26, 90), TMC(27, 90), TMC(28, 93),
   TMC(28, 98), TMC(29, 102), TMC(30, 104), TMC(31, 105), TMC(32, 108),
   TMC(32, 110), TMC(33, 33), TMC(34, 36), TMC(35, 111), TMC(36, 30),
   TMC(37, 112), TMC(38, 114), TMC(39, 97), TMC(40, 92), TMC(41, 115),
   TMC(42, 28), TMC(43, 26), TMC(44, 116), TMC(44, 117), TMC(44, 118),
   TMC(44, 119), TMC(44, 120), TMC(45, 23), TMC(46, 12), TMC(46, 122),
   TMC(47, 9), TMC(47, 30), TMC(48, 9), TMC(48, 30), TMC(49, 123),
   TMC(49, 124), TMC(50, 125), TMC(51, 126), TMC(51, 128), TMC(51, 130),
   TMC(52, 132), TMC(52, 130), TMC(53, 134), TMC(54, 135), TMC(55, 136),
   TMC(56, 130), TMC(57, 126), TMC(57, 138), TMC(58, 138), TMC(59, 65)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op buffer_def x = x
    val op buffer_def =
    ThmBind.DT(((("otp_mls",0),[("pair",[16])]),["DISK_THM"]),
               [ThmBind.read"%18%1%24%3%22%4%23%10%32%57%26$3@%29$2@%28$1@$0@5%30%94%34$3@%69%31@4%30%34%86$3@%69%45%37%37%56@6%69%31@3%53%42$3@%42%84$3@%69%45%37%56@5%42%84$3@%69%45%38%56@5%42%84$3@%69%45%37%37%56@6%42%84$3@%69%45%38%37%56@6%42%84$3@%69%45%37%38%56@6%42%84$3@%69%45%38%38%56@6%42%84$3@%69%45%37%37%37%56@7%42%84$3@%69%45%38%37%37%56@7%42%84$3@%69%45%37%38%37%56@7%39@11$1@4|@|@|@|@"])
  fun op mls_shift_one_def x = x
    val op mls_shift_one_def =
    ThmBind.DT(((("otp_mls",1),[]),[]),
               [ThmBind.read"%16%0%19%6%32%66$1@$0@2%35$0@%54$1@%87%45%37%37%37%56@5%31@%82$1@%67%45%37%56@6$0@3|@|@"])
  fun op shift_buffer_def x = x
    val op shift_buffer_def =
    ThmBind.DT(((("otp_mls",2),[]),[]),
               [ThmBind.read"%18%1%23%9%36%72$1@$0@2%55$1@$0%84$1@%69%45%37%56@6%55%84$1@%69%45%37%56@5$0%84$1@%69%45%38%56@6%55%84$1@%69%45%38%56@5$0%84$1@%69%45%37%37%56@7%55%84$1@%69%45%37%37%56@6$0%84$1@%69%45%38%37%56@7%55%84$1@%69%45%38%37%56@6$0%84$1@%69%45%37%38%56@7%55%84$1@%69%45%37%38%56@6$0%84$1@%69%45%38%38%56@7%55%84$1@%69%45%38%38%56@6$0%84$1@%69%45%37%37%37%56@8%55%84$1@%69%45%37%37%37%56@7$0%84$1@%69%45%38%37%37%56@8%55%84$1@%69%45%38%37%37%56@7$0%84$1@%69%45%37%38%37%56@8%55%84$1@%69%45%37%38%37%56@7%71%31@2$0@11|@|@"])
  fun op six_or_def x = x
    val op six_or_def =
    ThmBind.DT(((("otp_mls",4),[]),[]),
               [ThmBind.read"%17%14%20%7%33%73$1@$0@2%91$0%83$1@%68%45%38%56@6%91$0%83$1@%68%45%37%37%56@7%91$0%83$1@%68%45%38%37%56@7%91$0%83$1@%68%45%37%38%56@7%91$0%83$1@%68%45%38%38%56@7%91$0%83$1@%68%45%37%37%37%56@8%91$0%83$1@%68%45%38%37%37%56@8$0%83$1@%68%45%37%38%37%56@15|@|@"])
  fun op validate_datah_def x = x
    val op validate_datah_def =
    ThmBind.DT(((("otp_mls",5),[]),[]),
               [ThmBind.read"%17%14%21%8%33%75$1@$0@2%81%89%79%74$1@$0@3%45%37%37%37%56@7|@|@"])
  fun op validate_seqh_def x = x
    val op validate_seqh_def =
    ThmBind.DT(((("otp_mls",7),[]),[]),
               [ThmBind.read"%17%14%21%8%33%77$1@$0@2%89%79%85$0$1@2$0%83$1@%68%45%37%56@8%45%37%37%37%56@6|@|@"])
  fun op get_seq_no_def x = x
    val op get_seq_no_def =
    ThmBind.DT(((("otp_mls",9),[]),[]),
               [ThmBind.read"%18%15%23%9%34%59$1@$0@2%84%88%86%80$0$1@3%69%45%37%37%37%37%37%37%37%56@11%45%37%37%37%56@6%86%80$0%84$1@%69%45%37%56@7%69%45%37%37%37%37%37%37%37%56@12|@|@"])
  fun op mls_encrypt_def x = x
    val op mls_encrypt_def =
    ThmBind.DT(((("otp_mls",11),[]),[]),
               [ThmBind.read"%18%2%18%5%18%13%23%9%36%65$3@$2@$1@$0@2%55%84$3@%69%45%38%56@5%93$0%84$3@%69%45%38%56@6$0%84$2@%90%69%45%38%37%37%56@6$1@5%55%84$3@%69%45%37%37%56@6%93$0%84$3@%69%45%37%37%56@7$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%37%56@7%55%84$3@%69%45%38%37%56@6%93$0%84$3@%69%45%38%37%56@7$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%38%56@7%55%84$3@%69%45%37%38%56@6%93$0%84$3@%69%45%37%38%56@7$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%37%37%56@8%55%84$3@%69%45%38%38%56@6%93$0%84$3@%69%45%38%38%56@7$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%38%37%56@8%55%84$3@%69%45%37%37%37%56@7%93$0%84$3@%69%45%37%37%37%56@8$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%37%38%56@8%55%84$3@%69%45%38%37%37%56@7%93$0%84$3@%69%45%38%37%37%56@8$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%38%38%56@8%55%84$3@%69%45%37%38%37%56@7%93$0%84$3@%69%45%37%38%37%56@8$0%84%84$2@%90%69%45%38%37%37%56@6$1@3%69%45%37%37%37%56@9$0@9|@|@|@|@"])
  fun op otp_mls_shift_buffer x = x
    val op otp_mls_shift_buffer =
    ThmBind.DT(((("otp_mls",3),
                [("arithmetic",[1,2,19,27,68,93,221,274]),("bit",[5]),
                 ("bool",
                 [8,14,25,26,27,29,35,42,50,52,53,55,56,57,59,62,63,104,
                  123,128,142]),("combin",[8,19]),("fcp",[13,15]),
                 ("list",[29,299]),("m0_otp_decomp",[4,5,6]),
                 ("numeral",[0,3,5,7,8,9,15,16,17,21,24,28]),
                 ("numeral_bit",[2,23,34]),("otp_mls",[0,2]),
                 ("pair",[4,16]),("pred_set",[105]),("prog",[25]),
                 ("rich_list",[18,282,345]),("update",[17]),
                 ("words",
                 [49,51,69,144,231,256,324,325,327,329,331,342,356,380,387,
                  538,626,666,669])]),["DISK_THM"]),
               [ThmBind.read"%51%44@%52%52%52%52%52%52%50%62@2%60%3@3%63%11@3%61%4@%10@3%64%46@%12@3%49%64%48@4%58%57%26%12@%29%3@%28%4@%10@7%43%27%11@%41%70%45%37%37%38%37%37%37%38%37%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%56@5%41%70%45%37%37%38%37%37%37%37%37%37%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%56@6%41%70%45%37%37%38%37%37%37%37%38%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%56@6%41%70%45%37%37%38%37%37%37%38%37%37%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%37%56@7%41%70%45%37%37%38%37%37%37%38%38%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%37%56@7%41%70%45%37%37%38%37%37%37%37%38%37%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%38%56@7%41%70%45%37%37%38%37%37%37%37%37%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%38%56@7%41%70%45%37%37%38%37%37%37%38%38%37%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%37%37%56@8%41%70%45%37%37%38%37%37%37%38%37%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%37%37%56@8%41%70%45%37%37%38%37%37%37%37%37%38%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%38%37%56@8%41%70%45%37%37%38%37%37%37%37%38%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%38%37%56@8%41%70%45%37%37%38%37%37%37%38%37%38%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%37%38%56@8%41%70%45%37%37%38%37%37%37%38%38%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%37%38%56@8%41%70%45%37%37%38%37%37%37%37%38%38%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%38%38%56@8%41%70%45%37%37%38%37%37%37%37%37%37%38%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%38%38%56@8%41%70%45%37%37%38%37%37%37%38%38%38%37%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%37%37%37%56@9%41%70%45%37%37%38%37%37%37%38%37%37%38%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%37%37%37%56@9%41%70%45%37%37%38%37%37%37%37%37%37%38%37%37%38%38%56@19%43%27%84%11@%69%45%38%37%38%37%37%56@9%41%70%45%38%37%37%37%37%37%37%37%38%38%37%37%37%56@18%43%27%84%11@%69%45%38%38%38%37%37%56@9%41%70%45%37%37%38%37%37%37%38%37%37%38%37%37%38%38%56@19%40@21%52%52%52%52%52%50%62@2%60%25%3@%45%37%37%37%38%37%56@10%63%84%11@%69%45%38%37%37%38%37%56@11%61%4@%72%12@%10@4%64%46@%12@3%64%48@%69%31@4"])
  fun op otp_mls_validate_datah x = x
    val op otp_mls_validate_datah =
    ThmBind.DT(((("otp_mls",6),
                [("arithmetic",[27,93]),
                 ("bool",[8,25,26,35,50,52,55,57,62,104,123,142]),
                 ("m0_otp_decomp",[11,12,13]),("numeral",[0,3,5]),
                 ("otp_mls",[0,4,5]),("pair",[4,16]),("pred_set",[105]),
                 ("prog",[25]),("words",[205,294])]),["DISK_THM"]),
               [ThmBind.read"%51%44@%52%52%52%52%52%52%52%50%62@2%60%3@3%63%11@3%61%4@%10@3%64%46@%12@3%49%64%47@4%49%64%48@4%58%57%26%12@%29%3@%28%4@%10@7%43%27%11@%41%70%45%37%37%38%37%37%37%38%38%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%56@5%41%70%45%38%38%37%37%37%37%37%38%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%56@6%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%56@6%41%70%45%37%37%38%37%37%37%37%37%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%37%56@7%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%37%56@7%41%70%45%37%37%38%37%37%37%38%37%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%38%56@7%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%38%56@7%41%70%45%37%37%38%37%37%37%37%38%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%37%37%56@8%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%37%37%56@8%41%70%45%37%37%38%37%37%37%38%38%38%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%38%37%56@8%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%38%37%56@8%41%70%45%37%37%38%37%37%37%37%37%37%38%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%37%38%56@8%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%37%38%56@8%41%70%45%37%37%38%37%37%37%38%37%37%38%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%38%38%56@8%41%70%45%38%38%37%38%38%37%37%37%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%38%38%56@8%41%70%45%38%37%37%37%38%37%38%38%38%38%37%37%37%37%56@19%43%27%84%11@%69%45%38%37%37%37%37%56@9%41%70%45%38%37%37%37%38%37%38%38%38%37%37%56@16%43%27%84%11@%69%45%38%38%37%37%37%56@9%41%70%45%38%37%37%37%37%37%38%38%38%38%37%37%37%37%56@19%40@19%52%52%52%52%52%52%50%62@2%60%25%3@%45%38%38%37%38%56@9%63%84%11@%69%45%38%37%38%37%37%56@11%61%4@%10@3%64%46@%76%12@%10@4%64%47@%80%92%10%84%12@%69%45%38%56@6%92%10%84%12@%69%45%37%37%56@7%92%10%84%12@%69%45%38%37%56@7%92%10%84%12@%69%45%37%38%56@7%92%10%84%12@%69%45%38%38%56@7%92%10%84%12@%69%45%37%37%37%56@8%92%10%84%12@%69%45%38%37%37%56@8%10%84%12@%69%45%37%38%37%56@18%64%48@%80%10%84%12@%69%45%37%38%37%56@11"])
  fun op otp_mls_validate_seqh x = x
    val op otp_mls_validate_seqh =
    ThmBind.DT(((("otp_mls",8),
                [("arithmetic",[27,93]),
                 ("bool",[8,25,26,35,50,52,55,57,62,104,123,139,142]),
                 ("m0_otp_decomp",[18,19,20]),("numeral",[0,3,5]),
                 ("otp_mls",[0,7]),("pair",[4,16]),("pred_set",[105]),
                 ("prog",[25]),("words",[207,294])]),["DISK_THM"]),
               [ThmBind.read"%51%44@%52%52%52%52%52%52%50%62@2%60%3@3%63%11@3%61%4@%10@3%64%46@%12@3%49%64%48@4%58%57%26%12@%29%3@%28%4@%10@7%43%27%11@%41%70%45%37%37%38%37%37%37%37%37%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%56@5%41%70%45%38%37%37%37%37%37%38%37%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%56@6%41%70%45%38%37%37%38%38%37%37%37%37%37%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%56@6%41%70%45%38%37%37%37%37%37%38%38%38%37%37%56@16%40@5%52%52%52%52%52%50%62@2%60%25%3@%45%38%38%56@7%63%84%11@%69%45%38%37%37%56@9%61%4@%10@3%64%46@%78%12@%10@4%64%48@%80%10%12@5"])
  fun op otp_mls_get_seq_no x = x
    val op otp_mls_get_seq_no =
    ThmBind.DT(((("otp_mls",10),
                [("arithmetic",[27,93]),
                 ("bool",
                 [8,14,25,26,35,50,52,55,57,62,63,104,123,139,142]),
                 ("m0_otp_decomp",[25,26,27]),
                 ("numeral",[0,3,5,6,9,21,32,33,34,35,39,40]),
                 ("otp_mls",[0,9]),("pair",[4,16]),("pred_set",[105]),
                 ("prog",[25]),
                 ("words",[158,207,327,356,422,429])]),["DISK_THM"]),
               [ThmBind.read"%51%44@%52%52%52%52%52%52%52%50%62@2%60%3@3%63%11@3%61%4@%10@3%64%46@%12@3%49%64%47@4%49%64%48@4%58%57%26%12@%29%3@%28%4@%10@7%43%27%11@%41%70%45%38%38%38%38%38%38%38%38%37%38%37%37%37%56@18%43%27%84%11@%69%45%38%56@5%41%70%45%37%37%38%37%37%37%37%37%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%37%56@6%41%70%45%38%38%37%37%38%37%37%38%56@13%43%27%84%11@%69%45%38%38%56@6%41%70%45%37%37%38%38%38%37%38%38%56@13%43%27%84%11@%69%45%38%37%37%56@7%41%70%45%37%37%38%37%38%37%37%37%37%37%37%37%37%37%56@19%43%27%84%11@%69%45%38%38%37%56@7%41%70%45%37%37%37%37%37%37%37%38%37%38%37%37%37%56@18%43%27%84%11@%69%45%38%37%38%56@7%41%70%45%38%37%37%37%37%37%38%37%37%37%37%38%38%38%56@19%43%27%84%11@%69%45%38%38%38%56@7%41%70%45%38%37%37%37%38%37%37%37%37%37%37%37%37%37%56@19%43%27%84%11@%69%45%38%37%37%37%56@8%41%70%45%38%37%37%37%37%37%38%38%37%37%37%38%56@17%40@10%52%52%52%52%52%52%50%62@2%60%25%3@%45%37%37%38%56@8%63%84%11@%69%45%38%38%37%37%56@10%61%4@%10@3%64%46@%59%12@%10@4%64%47@%69%45%37%37%37%37%37%37%37%56@12%64%48@%86%88%80%10%12@3%45%37%37%37%56@6%88%69%45%38%38%38%38%38%38%38%56@10%45%38%38%56@8"])

  val _ = DB.bindl "otp_mls"
  [("buffer_def",buffer_def,DB.Def),
   ("mls_shift_one_def",mls_shift_one_def,DB.Def),
   ("shift_buffer_def",shift_buffer_def,DB.Def),
   ("six_or_def",six_or_def,DB.Def),
   ("validate_datah_def",validate_datah_def,DB.Def),
   ("validate_seqh_def",validate_seqh_def,DB.Def),
   ("get_seq_no_def",get_seq_no_def,DB.Def),
   ("mls_encrypt_def",mls_encrypt_def,DB.Def),
   ("otp_mls_shift_buffer",otp_mls_shift_buffer,DB.Thm),
   ("otp_mls_validate_datah",otp_mls_validate_datah,DB.Thm),
   ("otp_mls_validate_seqh",otp_mls_validate_seqh,DB.Thm),
   ("otp_mls_get_seq_no",otp_mls_get_seq_no,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "otp_mls",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "otp_mls.buffer_def otp_mls.validate_seqh_def otp_mls.mls_encrypt_def otp_mls.get_seq_no_def otp_mls.six_or_def otp_mls.validate_datah_def otp_mls.mls_shift_one_def otp_mls.shift_buffer_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "otp_mls",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO6.buffer3.%57OO13.mls_shift_one3.%66OO12.shift_buffer3.%72OO6.six_or3.%73OO14.validate_datah3.%75OO13.validate_seqh3.%77OO10.get_seq_no3.%59OO11.mls_encrypt3.%65"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val otp_mls_grammars = merge_grammars ["m0_otp_decomp"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="otp_mls"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val otp_mls_grammars = 
    Portable.## (addtyUDs,addtmUDs) otp_mls_grammars
  val _ = Parse.grammarDB_insert("otp_mls",otp_mls_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "otp_mls"
end
