structure otp_tlsTheory :> otp_tlsTheory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading otp_tlsTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (* Parents and ML dependencies *)
  local open wordsTheory
  in end;
  val _ = Theory.link_parents
          ("otp_tls",
          Arbnum.fromString "1534163804",
          Arbnum.fromString "185054")
          [("words",
           Arbnum.fromString "1492708538",
           Arbnum.fromString "576120")];
  val _ = Theory.incorporate_types "otp_tls" [("otp_state", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("fcp", "cart"), ID("fcp", "bit0"),
   ID("one", "one"), ID("min", "bool"), ID("num", "num"),
   ID("list", "list"), ID("otp_tls", "otp_state"),
   ID("ind_type", "recspace"), ID("pair", "prod"), ID("fcp", "bit1"),
   ID("min", "ind"), ID("bool", "!"), ID("arithmetic", "*"),
   ID("arithmetic", "+"), ID("pair", ","), ID("bool", "/\\"),
   ID("num", "0"), ID("prim_rec", "<"), ID("min", "="), ID("min", "==>"),
   ID("bool", "?"), ID("list", "APPEND"), ID("bool", "ARB"),
   ID("arithmetic", "BIT1"), ID("arithmetic", "BIT2"),
   ID("ind_type", "BOTTOM"), ID("bool", "COND"), ID("list", "CONS"),
   ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"), ID("bool", "F"),
   ID("combin", "K"), ID("bool", "LET"), ID("list", "NIL"),
   ID("arithmetic", "NUMERAL"), ID("bool", "T"), ID("list", "TL"),
   ID("bool", "TYPE_DEFINITION"), ID("combin", "UPDATE"),
   ID("arithmetic", "ZERO"), ID("words", "bit_field_insert"),
   ID("otp_tls", "buffer"), ID("otp_tls", "encrypt"),
   ID("otp_tls", "encrypt_buffer"), ID("otp_tls", "get_seq_no"),
   ID("list", "list_size"), ID("bool", "literal_case"),
   ID("otp_tls", "max_seq"), ID("words", "n2w"), ID("combin", "o"),
   ID("otp_tls", "otp_state_Buffer"),
   ID("otp_tls", "otp_state_Buffer_fupd"), ID("otp_tls", "otp_state_CASE"),
   ID("otp_tls", "otp_state_CurrSeq"),
   ID("otp_tls", "otp_state_CurrSeq_fupd"), ID("otp_tls", "otp_state_In"),
   ID("otp_tls", "otp_state_In_fupd"), ID("otp_tls", "otp_state_Key"),
   ID("otp_tls", "otp_state_Key_fupd"), ID("otp_tls", "otp_state_Out"),
   ID("otp_tls", "otp_state_Out_fupd"), ID("otp_tls", "otp_state_size"),
   ID("otp_tls", "put_val_in_buf"), ID("otp_tls", "recordtype.otp_state"),
   ID("otp_tls", "seq_in_order"), ID("otp_tls", "shift_buffer"),
   ID("otp_tls", "test_buffer"), ID("otp_tls", "tls_otp_spec"),
   ID("otp_tls", "uart_read"), ID("otp_tls", "uart_write_buffer"),
   ID("otp_tls", "valid"), ID("words", "w2n"), ID("words", "word_and"),
   ID("words", "word_msb"), ID("words", "word_xor"),
   ID("otp_tls", "zero_datah")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [3], TYOP [2, 0], TYOP [2, 1], TYOP [2, 2], TYOP [4],
   TYOP [1, 4, 3], TYOP [5], TYOP [0, 6, 5], TYOP [0, 7, 7],
   TYOP [0, 7, 4], TYOP [6, 5], TYOP [0, 7, 10], TYOP [0, 10, 11],
   TYV "'a", TYOP [6, 13], TYOP [0, 14, 13], TYOP [7], TYOP [0, 16, 16],
   TYOP [0, 6, 4], TYOP [0, 6, 18], TYOP [0, 7, 16], TYOP [0, 10, 20],
   TYOP [0, 10, 21], TYOP [0, 6, 22], TYOP [0, 7, 23], TYOP [0, 5, 7],
   TYOP [0, 7, 25], TYOP [0, 16, 6], TYOP [0, 10, 10], TYOP [0, 28, 17],
   TYOP [0, 16, 10], TYOP [0, 8, 17], TYOP [0, 16, 7], TYOP [0, 6, 6],
   TYOP [0, 33, 17], TYOP [0, 7, 13], TYOP [0, 10, 35], TYOP [0, 10, 36],
   TYOP [0, 6, 37], TYOP [0, 7, 38], TYOP [0, 39, 13], TYOP [0, 16, 40],
   TYOP [0, 7, 6], TYOP [0, 6, 7], TYOP [0, 7, 43], TYOP [0, 7, 44],
   TYOP [1, 4, 13], TYOP [0, 46, 46], TYOP [0, 46, 47], TYOP [9, 10, 7],
   TYOP [9, 10, 49], TYOP [9, 6, 50], TYOP [9, 7, 51], TYOP [8, 52],
   TYOP [0, 53, 4], TYOP [0, 16, 4], TYOP [10, 0], TYOP [10, 56],
   TYOP [2, 57], TYOP [1, 4, 58], TYOP [0, 16, 13], TYOP [0, 13, 16],
   TYOP [11], TYOP [0, 10, 9], TYOP [0, 10, 63], TYOP [0, 6, 64],
   TYOP [0, 7, 65], TYOP [0, 62, 66], TYOP [0, 16, 53], TYOP [0, 13, 4],
   TYOP [0, 69, 4], TYOP [0, 46, 4], TYOP [0, 71, 4], TYOP [0, 5, 4],
   TYOP [0, 73, 4], TYOP [0, 61, 4], TYOP [0, 75, 4], TYOP [0, 8, 4],
   TYOP [0, 77, 4], TYOP [0, 39, 4], TYOP [0, 79, 4], TYOP [0, 28, 4],
   TYOP [0, 81, 4], TYOP [0, 9, 4], TYOP [0, 33, 4], TYOP [0, 84, 4],
   TYOP [0, 55, 4], TYOP [0, 86, 4], TYOP [0, 54, 4], TYOP [0, 88, 4],
   TYOP [0, 14, 4], TYOP [0, 90, 4], TYOP [0, 10, 4], TYOP [0, 92, 4],
   TYOP [0, 18, 4], TYOP [0, 6, 33], TYOP [0, 51, 52], TYOP [0, 7, 96],
   TYOP [0, 7, 49], TYOP [0, 10, 98], TYOP [0, 49, 50], TYOP [0, 10, 100],
   TYOP [0, 50, 51], TYOP [0, 6, 102], TYOP [0, 4, 4], TYOP [0, 4, 104],
   TYOP [0, 13, 69], TYOP [0, 46, 71], TYOP [0, 5, 73], TYOP [0, 61, 75],
   TYOP [0, 7, 9], TYOP [0, 17, 4], TYOP [0, 17, 111], TYOP [0, 10, 92],
   TYOP [0, 16, 55], TYOP [0, 53, 54], TYOP [0, 60, 4], TYOP [0, 116, 4],
   TYOP [0, 68, 4], TYOP [0, 118, 4], TYOP [0, 10, 28], TYOP [0, 5, 5],
   TYOP [0, 5, 121], TYOP [0, 4, 122], TYOP [0, 16, 17], TYOP [0, 4, 124],
   TYOP [0, 14, 14], TYOP [0, 13, 126], TYOP [0, 5, 28], TYOP [0, 6, 53],
   TYOP [0, 129, 53], TYOP [0, 52, 130], TYOP [0, 6, 131], TYOP [0, 7, 8],
   TYOP [0, 59, 6], TYOP [0, 134, 134], TYOP [0, 20, 20], TYOP [0, 10, 16],
   TYOP [0, 137, 137], TYOP [0, 6, 16], TYOP [0, 139, 139],
   TYOP [0, 17, 17], TYOP [0, 54, 118], TYOP [0, 5, 8], TYOP [0, 6, 143],
   TYOP [0, 59, 59], TYOP [0, 5, 145], TYOP [0, 6, 146], TYOP [0, 6, 147],
   TYOP [0, 10, 6], TYOP [0, 5, 6], TYOP [0, 150, 149], TYOP [0, 6, 59],
   TYOP [0, 8, 8], TYOP [0, 8, 153], TYOP [0, 28, 28], TYOP [0, 28, 155],
   TYOP [0, 33, 33], TYOP [0, 33, 157], TYOP [0, 61, 61],
   TYOP [0, 17, 159], TYOP [0, 17, 141], TYOP [0, 10, 5]]
  end
  val _ = Theory.incorporate_consts "otp_tls" tyvector
     [("zero_datah", 8), ("valid", 9), ("uart_write_buffer", 12),
      ("uart_read", 15), ("tls_otp_spec", 17), ("test_buffer", 7),
      ("shift_buffer", 8), ("seq_in_order", 19),
      ("recordtype.otp_state", 24), ("put_val_in_buf", 26),
      ("otp_state_size", 27), ("otp_state_Out_fupd", 29),
      ("otp_state_Out", 30), ("otp_state_Key_fupd", 31),
      ("otp_state_Key", 32), ("otp_state_In_fupd", 29),
      ("otp_state_In", 30), ("otp_state_CurrSeq_fupd", 34),
      ("otp_state_CurrSeq", 27), ("otp_state_CASE", 41),
      ("otp_state_Buffer_fupd", 31), ("otp_state_Buffer", 32),
      ("max_seq", 6), ("get_seq_no", 42), ("encrypt_buffer", 45),
      ("encrypt", 48), ("buffer", 7)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'otp_state'", 54), TMV("Buffer", 7), TMV("CurrSeq", 6),
   TMV("In", 10), TMV("Key", 7), TMV("M", 16), TMV("M'", 16),
   TMV("Out", 10), TMV("P", 55), TMV("a", 59), TMV("a0", 7), TMV("a0'", 7),
   TMV("a0'", 53), TMV("a1", 6), TMV("a1'", 6), TMV("a2", 10),
   TMV("a2'", 10), TMV("a3", 10), TMV("a3'", 10), TMV("a4", 7),
   TMV("a4'", 7), TMV("b", 5), TMV("buf", 7), TMV("curr", 6), TMV("f", 8),
   TMV("f", 39), TMV("f", 28), TMV("f", 7), TMV("f", 33), TMV("f'", 39),
   TMV("f0", 7), TMV("f01", 7), TMV("f02", 7), TMV("f1", 8), TMV("f1", 28),
   TMV("f1", 7), TMV("f1", 33), TMV("f2", 7), TMV("fn", 60), TMV("g", 8),
   TMV("g", 28), TMV("g", 33), TMV("h", 61), TMV("k", 46), TMV("key", 7),
   TMV("l", 10), TMV("l0", 10), TMV("l01", 10), TMV("l02", 10),
   TMV("l1", 10), TMV("l2", 10), TMV("n", 6), TMV("n1", 6), TMV("n2", 6),
   TMV("new", 6), TMV("newBuf", 7), TMV("newOut", 10), TMV("o", 16),
   TMV("o1", 16), TMV("o2", 16), TMV("oo", 16), TMV("otp_state", 62),
   TMV("out", 10), TMV("rcd", 16), TMV("record", 67), TMV("rep", 68),
   TMV("s", 16), TMV("s'", 16), TMV("seq", 6), TMV("seq_no", 6),
   TMV("v", 46), TMV("v", 5), TMV("v", 6), TMV("x", 13), TMV("x", 5),
   TMV("x", 7), TMV("x", 10), TMV("x", 16), TMV("xs", 14), TMC(12, 70),
   TMC(12, 72), TMC(12, 74), TMC(12, 76), TMC(12, 78), TMC(12, 80),
   TMC(12, 82), TMC(12, 83), TMC(12, 85), TMC(12, 87), TMC(12, 89),
   TMC(12, 91), TMC(12, 93), TMC(12, 94), TMC(12, 86), TMC(12, 88),
   TMC(13, 95), TMC(14, 95), TMC(15, 97), TMC(15, 99), TMC(15, 101),
   TMC(15, 103), TMC(16, 105), TMC(17, 6), TMC(18, 19), TMC(19, 106),
   TMC(19, 105), TMC(19, 107), TMC(19, 108), TMC(19, 109), TMC(19, 110),
   TMC(19, 112), TMC(19, 113), TMC(19, 19), TMC(19, 114), TMC(19, 115),
   TMC(20, 105), TMC(21, 83), TMC(21, 117), TMC(21, 119), TMC(21, 93),
   TMC(21, 94), TMC(21, 86), TMC(22, 120), TMC(23, 13), TMC(23, 5),
   TMC(23, 16), TMC(24, 33), TMC(25, 33), TMC(26, 53), TMC(27, 123),
   TMC(27, 125), TMC(28, 127), TMC(28, 128), TMC(29, 132), TMC(30, 104),
   TMC(31, 4), TMC(32, 133), TMC(32, 120), TMC(32, 95), TMC(33, 135),
   TMC(33, 136), TMC(33, 138), TMC(33, 140), TMC(33, 141), TMC(34, 14),
   TMC(34, 10), TMC(35, 33), TMC(36, 4), TMC(37, 28), TMC(38, 142),
   TMC(39, 144), TMC(40, 6), TMC(41, 148), TMC(42, 7), TMC(43, 48),
   TMC(43, 122), TMC(44, 45), TMC(45, 42), TMC(46, 151), TMC(47, 8),
   TMC(48, 6), TMC(49, 7), TMC(49, 152), TMC(50, 154), TMC(50, 156),
   TMC(50, 158), TMC(50, 160), TMC(50, 161), TMC(51, 32), TMC(52, 31),
   TMC(53, 41), TMC(54, 27), TMC(55, 34), TMC(56, 30), TMC(57, 29),
   TMC(58, 32), TMC(59, 31), TMC(60, 30), TMC(61, 29), TMC(62, 27),
   TMC(63, 26), TMC(64, 24), TMC(65, 19), TMC(66, 8), TMC(67, 7),
   TMC(68, 17), TMC(69, 15), TMC(69, 162), TMC(70, 12), TMC(71, 9),
   TMC(72, 134), TMC(73, 122), TMC(74, 73), TMC(75, 48), TMC(76, 8)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op otp_state_TY_DEF x = x
    val op otp_state_TY_DEF =
    ThmBind.DT(((("otp_tls",0),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%118%65%149%12%89%0%115%94%12%115%116%10%120%13%119%15%119%17%116%19%114$5@%10%13%15%17%19%133%102@%97$4@%100$3@%99$2@%98$1@$0@5%51%128|@|||||$4@$3@$2@$1@$0@2|@|@|@|@|@2$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op otp_state_case_def x = x
    val op otp_state_case_def =
    ThmBind.DT(((("otp_tls",4),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%10%92%13%91%15%91%17%86%19%84%25%104%170%181$5@$4@$3@$2@$1@2$0@2$0$5@$4@$3@$2@$1@2|@|@|@|@|@|@"])
  fun op otp_state_size_def x = x
    val op otp_state_size_def =
    ThmBind.DT(((("otp_tls",5),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%10%92%13%91%15%91%17%86%19%112%179%181$4@$3@$2@$1@$0@3%96%146%126%151@3%96$3@%96%158%71%102|@$2@2%158%71%102|@$1@5|@|@|@|@|@"])
  fun op otp_state_Buffer x = x
    val op otp_state_Buffer =
    ThmBind.DT(((("otp_tls",6),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%27%92%51%91%45%91%46%86%30%109%168%181$4@$3@$2@$1@$0@3$4@|@|@|@|@|@"])
  fun op otp_state_CurrSeq x = x
    val op otp_state_CurrSeq =
    ThmBind.DT(((("otp_tls",7),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%27%92%51%91%45%91%46%86%30%112%171%181$4@$3@$2@$1@$0@3$3@|@|@|@|@|@"])
  fun op otp_state_In x = x
    val op otp_state_In =
    ThmBind.DT(((("otp_tls",8),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%27%92%51%91%45%91%46%86%30%111%173%181$4@$3@$2@$1@$0@3$2@|@|@|@|@|@"])
  fun op otp_state_Out x = x
    val op otp_state_Out =
    ThmBind.DT(((("otp_tls",9),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%27%92%51%91%45%91%46%86%30%111%177%181$4@$3@$2@$1@$0@3$1@|@|@|@|@|@"])
  fun op otp_state_Key x = x
    val op otp_state_Key =
    ThmBind.DT(((("otp_tls",10),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%27%92%51%91%45%91%46%86%30%109%175%181$4@$3@$2@$1@$0@3$0@|@|@|@|@|@"])
  fun op otp_state_Buffer_fupd x = x
    val op otp_state_Buffer_fupd =
    ThmBind.DT(((("otp_tls",12),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%83%33%86%27%92%51%91%45%91%46%86%30%113%169$5@%181$4@$3@$2@$1@$0@3%181$5$4@2$3@$2@$1@$0@2|@|@|@|@|@|@"])
  fun op otp_state_CurrSeq_fupd x = x
    val op otp_state_CurrSeq_fupd =
    ThmBind.DT(((("otp_tls",13),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%87%36%86%27%92%51%91%45%91%46%86%30%113%172$5@%181$4@$3@$2@$1@$0@3%181$4@$5$3@2$2@$1@$0@2|@|@|@|@|@|@"])
  fun op otp_state_In_fupd x = x
    val op otp_state_In_fupd =
    ThmBind.DT(((("otp_tls",14),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%85%34%86%27%92%51%91%45%91%46%86%30%113%174$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$5$2@2$1@$0@2|@|@|@|@|@|@"])
  fun op otp_state_Out_fupd x = x
    val op otp_state_Out_fupd =
    ThmBind.DT(((("otp_tls",15),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%85%34%86%27%92%51%91%45%91%46%86%30%113%178$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$2@$5$1@2$0@2|@|@|@|@|@|@"])
  fun op otp_state_Key_fupd x = x
    val op otp_state_Key_fupd =
    ThmBind.DT(((("otp_tls",16),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%83%33%86%27%92%51%91%45%91%46%86%30%113%176$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$2@$1@$5$0@3|@|@|@|@|@|@"])
  fun op max_seq_def x = x
    val op max_seq_def =
    ThmBind.DT(((("otp_tls",35),[]),[]),
               [ThmBind.read"%112%160@%146%126%126%126%126%126%126%126%126%126%126%126%126%126%126%151@16"])
  fun op buffer_def x = x
    val op buffer_def =
    ThmBind.DT(((("otp_tls",36),[]),[]),
               [ThmBind.read"%92%51%107%153$0@2%159%72%129%112$0@%102@2%161%102@2%129%112$0@%146%126%151@4%161%102@2%129%112$0@%146%127%151@4%161%102@2%129%112$0@%146%126%126%151@5%161%102@2%129%112$0@%146%127%126%151@5%161%102@2%129%112$0@%146%126%127%151@5%161%102@2%129%112$0@%146%127%127%151@5%161%102@2%129%112$0@%146%126%126%126%151@6%161%102@2%129%112$0@%146%127%126%126%151@6%161%102@2%129%112$0@%146%126%127%126%151@6%161%102@2%124@10|@$0@2|@"])
  fun op shift_buffer_def x = x
    val op shift_buffer_def =
    ThmBind.DT(((("otp_tls",37),[]),[]),
               [ThmBind.read"%86%27%109%183$0@2%150%102@$0%146%126%151@4%150%146%126%151@3$0%146%127%151@4%150%146%127%151@3$0%146%126%126%151@5%150%146%126%126%151@4$0%146%127%126%151@5%150%146%127%126%151@4$0%146%126%127%151@5%150%146%126%127%151@4$0%146%127%127%151@5%150%146%127%127%151@4$0%146%126%126%126%151@6%150%146%126%126%126%151@5$0%146%127%126%126%151@6%150%146%127%126%126%151@5$0%146%126%127%126%151@6%150%146%126%127%126%151@5%161%102@2$0@11|@"])
  fun op put_val_in_buf_def x = x
    val op put_val_in_buf_def =
    ThmBind.DT(((("otp_tls",38),[]),[]),
               [ThmBind.read"%86%27%81%21%109%180$1@$0@2%150%146%126%127%126%151@5$0@$1@2|@|@"])
  fun op uart_read_def x = x
    val op uart_read_def =
    ThmBind.DT(((("otp_tls",40),[("list",[13])]),["DISK_THM"]),
               [ThmBind.read"%101%104%186%144@2%123@2%79%73%90%78%104%186%131$1@$0@3$1@|@|@2"])
  fun op valid_def x = x
    val op valid_def =
    ThmBind.DT(((("otp_tls",41),[]),[]),
               [ThmBind.read"%86%22%105%189$0@2%101%105%192$0%102@3%147@2%101%105%192$0%146%126%151@5%147@2%101%105%192$0%146%127%151@5%135@2%101%105%192$0%146%126%126%151@6%135@2%101%105%192$0%146%127%126%151@6%135@2%101%105%192$0%146%126%127%151@6%135@2%101%105%192$0%146%127%127%151@6%135@2%101%105%192$0%146%126%126%126%151@7%135@2%101%105%192$0%146%127%126%126%151@7%135@2%105%192$0%146%126%127%126%151@7%135@11|@"])
  fun op get_seq_no_def x = x
    val op get_seq_no_def =
    ThmBind.DT(((("otp_tls",42),[]),[]),
               [ThmBind.read"%86%22%112%157$0@2%139%9%190%152%146%127%127%151@4%102@$1%146%126%151@4$0@2|@%152%146%126%127%127%151@5%146%126%126%126%151@5$0%102@2%162%102@4|@"])
  fun op test_buffer_def x = x
    val op test_buffer_def =
    ThmBind.DT(((("otp_tls",43),[]),[]),
               [ThmBind.read"%109%184@%150%102@%161%146%126%126%126%126%126%126%126%126%151@11%150%146%126%151@3%161%146%126%126%126%126%126%126%126%126%151@11%153@3"])
  fun op seq_in_order_def x = x
    val op seq_in_order_def =
    ThmBind.DT(((("otp_tls",44),[]),[]),
               [ThmBind.read"%92%23%92%54%105%182$1@$0@2%101%103$1@$0@2%103$1@%160@3|@|@"])
  fun op encrypt_def x = x
    val op encrypt_def =
    ThmBind.DT(((("otp_tls",45),[]),[]),
               [ThmBind.read"%80%70%80%43%106%154$1@$0@2%193$1@$0@2|@|@"])
  fun op encrypt_buffer_def x = x
    val op encrypt_buffer_def =
    ThmBind.DT(((("otp_tls",46),[]),[]),
               [ThmBind.read"%86%27%86%44%92%68%109%156$2@$1@$0@2%150%146%127%151@3%155$2%146%127%151@4$1%95%146%127%126%126%151@5$0@4%150%146%126%126%151@4%155$2%146%126%126%151@5$1%96%95%146%127%126%126%151@5$0@2%146%126%151@6%150%146%127%126%151@4%155$2%146%127%126%151@5$1%96%95%146%127%126%126%151@5$0@2%146%127%151@6%150%146%126%127%151@4%155$2%146%126%127%151@5$1%96%95%146%127%126%126%151@5$0@2%146%126%126%151@7%150%146%127%127%151@4%155$2%146%127%127%151@5$1%96%95%146%127%126%126%151@5$0@2%146%127%126%151@7%150%146%126%126%126%151@5%155$2%146%126%126%126%151@6$1%96%95%146%127%126%126%151@5$0@2%146%126%127%151@7%150%146%127%126%126%151@5%155$2%146%127%126%126%151@6$1%96%95%146%127%126%126%151@5$0@2%146%127%127%151@7%150%146%126%127%126%151@5%155$2%146%126%127%126%151@6$1%96%95%146%127%126%126%151@5$0@2%146%126%126%126%151@8$2@9|@|@|@"])
  fun op zero_datah_def x = x
    val op zero_datah_def =
    ThmBind.DT(((("otp_tls",47),[]),[]),
               [ThmBind.read"%86%27%109%194$0@2%150%146%127%151@3%191$0%146%127%151@4%161%146%126%126%126%126%126%126%126%151@11%150%146%126%126%151@4%191$0%146%126%126%151@5%161%146%126%126%126%126%126%126%126%151@11%150%146%127%126%151@4%191$0%146%127%126%151@5%161%146%126%126%126%126%126%126%126%151@11%150%146%126%127%151@4%191$0%146%126%127%151@5%161%146%126%126%126%126%126%126%126%151@11%150%146%127%127%151@4%191$0%146%127%127%151@5%161%146%126%126%126%126%126%126%126%151@11%150%146%126%126%126%151@5%191$0%146%126%126%126%151@6%161%146%126%126%126%126%126%126%126%151@11%150%146%127%126%126%151@5%191$0%146%127%126%126%151@6%161%146%126%126%126%126%126%126%126%151@11%150%146%126%127%126%151@5%191$0%146%126%127%126%151@6%161%146%126%126%126%126%126%126%126%151@11$0@9|@"])
  fun op uart_write_buffer_def x = x
    val op uart_write_buffer_def =
    ThmBind.DT(((("otp_tls",48),[]),[]),
               [ThmBind.read"%91%62%86%22%111%188$1@$0@2%122$1@%132$0%102@2%132$0%146%126%151@4%132$0%146%127%151@4%132$0%146%126%126%151@5%132$0%146%127%126%151@5%132$0%146%126%127%151@5%132$0%146%127%127%151@5%132$0%146%126%126%126%151@6%132$0%146%127%126%126%151@6%132$0%146%126%127%126%151@6%145@12|@|@"])
  fun op tls_otp_spec_def x = x
    val op tls_otp_spec_def =
    ThmBind.DT(((("otp_tls",50),[]),[]),
               [ThmBind.read"%93%66%113%185$0@2%143%67%130%189%168$0@3%142%69%130%182%171$1@2$0@2%140%55%141%56%169%136$1@2%172%138$2@2%178%137$0@2$3@3|@%188%177$2@2$0@2|@%194%156%168$1@2%175$1@2$0@4$1@|@%157%168$0@4$0@|@%169%136%180%183%168$0@3%187%173$0@5%174%137%148%173$0@4$0@4|@"])
  fun op otp_state_accessors x = x
    val op otp_state_accessors =
    ThmBind.DT(((("otp_tls",11),[("otp_tls",[6,7,8,9,10])]),["DISK_THM"]),
               [ThmBind.read"%101%86%27%92%51%91%45%91%46%86%30%109%168%181$4@$3@$2@$1@$0@3$4@|@|@|@|@|@2%101%86%27%92%51%91%45%91%46%86%30%112%171%181$4@$3@$2@$1@$0@3$3@|@|@|@|@|@2%101%86%27%92%51%91%45%91%46%86%30%111%173%181$4@$3@$2@$1@$0@3$2@|@|@|@|@|@2%101%86%27%92%51%91%45%91%46%86%30%111%177%181$4@$3@$2@$1@$0@3$1@|@|@|@|@|@2%86%27%92%51%91%45%91%46%86%30%109%175%181$4@$3@$2@$1@$0@3$0@|@|@|@|@|@5"])
  fun op otp_state_fn_updates x = x
    val op otp_state_fn_updates =
    ThmBind.DT(((("otp_tls",17),
                [("otp_tls",[12,13,14,15,16])]),["DISK_THM"]),
               [ThmBind.read"%101%83%33%86%27%92%51%91%45%91%46%86%30%113%169$5@%181$4@$3@$2@$1@$0@3%181$5$4@2$3@$2@$1@$0@2|@|@|@|@|@|@2%101%87%36%86%27%92%51%91%45%91%46%86%30%113%172$5@%181$4@$3@$2@$1@$0@3%181$4@$5$3@2$2@$1@$0@2|@|@|@|@|@|@2%101%85%34%86%27%92%51%91%45%91%46%86%30%113%174$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$5$2@2$1@$0@2|@|@|@|@|@|@2%101%85%34%86%27%92%51%91%45%91%46%86%30%113%178$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$2@$5$1@2$0@2|@|@|@|@|@|@2%83%33%86%27%92%51%91%45%91%46%86%30%113%176$5@%181$4@$3@$2@$1@$0@3%181$4@$3@$2@$1@$5$0@3|@|@|@|@|@|@5"])
  fun op otp_state_accfupds x = x
    val op otp_state_accfupds =
    ThmBind.DT(((("otp_tls",18),
                [("bool",[25,26,55,180]),
                 ("otp_tls",[1,2,3,11,17])]),["DISK_THM"]),
               [ThmBind.read"%101%93%57%87%28%109%168%172$0@$1@3%168$1@2|@|@2%101%93%57%85%26%109%168%174$0@$1@3%168$1@2|@|@2%101%93%57%85%26%109%168%178$0@$1@3%168$1@2|@|@2%101%93%57%83%24%109%168%176$0@$1@3%168$1@2|@|@2%101%93%57%83%24%112%171%169$0@$1@3%171$1@2|@|@2%101%93%57%85%26%112%171%174$0@$1@3%171$1@2|@|@2%101%93%57%85%26%112%171%178$0@$1@3%171$1@2|@|@2%101%93%57%83%24%112%171%176$0@$1@3%171$1@2|@|@2%101%93%57%83%24%111%173%169$0@$1@3%173$1@2|@|@2%101%93%57%87%28%111%173%172$0@$1@3%173$1@2|@|@2%101%93%57%85%26%111%173%178$0@$1@3%173$1@2|@|@2%101%93%57%83%24%111%173%176$0@$1@3%173$1@2|@|@2%101%93%57%83%24%111%177%169$0@$1@3%177$1@2|@|@2%101%93%57%87%28%111%177%172$0@$1@3%177$1@2|@|@2%101%93%57%85%26%111%177%174$0@$1@3%177$1@2|@|@2%101%93%57%83%24%111%177%176$0@$1@3%177$1@2|@|@2%101%93%57%83%24%109%175%169$0@$1@3%175$1@2|@|@2%101%93%57%87%28%109%175%172$0@$1@3%175$1@2|@|@2%101%93%57%85%26%109%175%174$0@$1@3%175$1@2|@|@2%101%93%57%85%26%109%175%178$0@$1@3%175$1@2|@|@2%101%93%57%83%24%109%168%169$0@$1@3$0%168$1@3|@|@2%101%93%57%87%28%112%171%172$0@$1@3$0%171$1@3|@|@2%101%93%57%85%26%111%173%174$0@$1@3$0%173$1@3|@|@2%101%93%57%85%26%111%177%178$0@$1@3$0%177$1@3|@|@2%93%57%83%24%109%175%176$0@$1@3$0%175$1@3|@|@25"])
  fun op otp_state_fupdfupds x = x
    val op otp_state_fupdfupds =
    ThmBind.DT(((("otp_tls",19),
                [("bool",[25,26,55,180]),("combin",[8]),
                 ("otp_tls",[1,2,3,17])]),["DISK_THM"]),
               [ThmBind.read"%101%93%57%83%39%83%24%113%169$0@%169$1@$2@3%169%163$0@$1@2$2@2|@|@|@2%101%93%57%87%41%87%28%113%172$0@%172$1@$2@3%172%165$0@$1@2$2@2|@|@|@2%101%93%57%85%40%85%26%113%174$0@%174$1@$2@3%174%164$0@$1@2$2@2|@|@|@2%101%93%57%85%40%85%26%113%178$0@%178$1@$2@3%178%164$0@$1@2$2@2|@|@|@2%93%57%83%39%83%24%113%176$0@%176$1@$2@3%176%163$0@$1@2$2@2|@|@|@5"])
  fun op otp_state_fupdfupds_comp x = x
    val op otp_state_fupdfupds_comp =
    ThmBind.DT(((("otp_tls",20),
                [("bool",[14,25,26,55,57,180]),("combin",[8,9]),
                 ("otp_tls",[1,2,3,17])]),["DISK_THM"]),
               [ThmBind.read"%101%101%83%39%83%24%110%167%169$0@2%169$1@3%169%163$0@$1@3|@|@2%82%42%83%39%83%24%108%166%169$0@2%166%169$1@2$2@3%166%169%163$0@$1@3$2@2|@|@|@3%101%101%87%41%87%28%110%167%172$0@2%172$1@3%172%165$0@$1@3|@|@2%82%42%87%41%87%28%108%166%172$0@2%166%172$1@2$2@3%166%172%165$0@$1@3$2@2|@|@|@3%101%101%85%40%85%26%110%167%174$0@2%174$1@3%174%164$0@$1@3|@|@2%82%42%85%40%85%26%108%166%174$0@2%166%174$1@2$2@3%166%174%164$0@$1@3$2@2|@|@|@3%101%101%85%40%85%26%110%167%178$0@2%178$1@3%178%164$0@$1@3|@|@2%82%42%85%40%85%26%108%166%178$0@2%166%178$1@2$2@3%166%178%164$0@$1@3$2@2|@|@|@3%101%83%39%83%24%110%167%176$0@2%176$1@3%176%163$0@$1@3|@|@2%82%42%83%39%83%24%108%166%176$0@2%166%176$1@2$2@3%166%176%163$0@$1@3$2@2|@|@|@6"])
  fun op otp_state_fupdcanon x = x
    val op otp_state_fupdcanon =
    ThmBind.DT(((("otp_tls",21),
                [("bool",[25,26,55,180]),
                 ("otp_tls",[1,2,3,17])]),["DISK_THM"]),
               [ThmBind.read"%101%93%57%83%39%87%28%113%172$0@%169$1@$2@3%169$1@%172$0@$2@3|@|@|@2%101%93%57%83%39%85%26%113%174$0@%169$1@$2@3%169$1@%174$0@$2@3|@|@|@2%101%93%57%87%41%85%26%113%174$0@%172$1@$2@3%172$1@%174$0@$2@3|@|@|@2%101%93%57%83%39%85%26%113%178$0@%169$1@$2@3%169$1@%178$0@$2@3|@|@|@2%101%93%57%87%41%85%26%113%178$0@%172$1@$2@3%172$1@%178$0@$2@3|@|@|@2%101%93%57%85%40%85%26%113%178$0@%174$1@$2@3%174$1@%178$0@$2@3|@|@|@2%101%93%57%83%39%83%24%113%176$0@%169$1@$2@3%169$1@%176$0@$2@3|@|@|@2%101%93%57%87%41%83%24%113%176$0@%172$1@$2@3%172$1@%176$0@$2@3|@|@|@2%101%93%57%85%40%83%24%113%176$0@%174$1@$2@3%174$1@%176$0@$2@3|@|@|@2%93%57%85%40%83%24%113%176$0@%178$1@$2@3%178$1@%176$0@$2@3|@|@|@10"])
  fun op otp_state_fupdcanon_comp x = x
    val op otp_state_fupdcanon_comp =
    ThmBind.DT(((("otp_tls",22),
                [("bool",[14,25,26,55,57,180]),("combin",[8,9]),
                 ("otp_tls",[1,2,3,17])]),["DISK_THM"]),
               [ThmBind.read"%101%101%83%39%87%28%110%167%172$0@2%169$1@3%167%169$1@2%172$0@3|@|@2%82%42%83%39%87%28%108%166%172$0@2%166%169$1@2$2@3%166%169$1@2%166%172$0@2$2@3|@|@|@3%101%101%83%39%85%26%110%167%174$0@2%169$1@3%167%169$1@2%174$0@3|@|@2%82%42%83%39%85%26%108%166%174$0@2%166%169$1@2$2@3%166%169$1@2%166%174$0@2$2@3|@|@|@3%101%101%87%41%85%26%110%167%174$0@2%172$1@3%167%172$1@2%174$0@3|@|@2%82%42%87%41%85%26%108%166%174$0@2%166%172$1@2$2@3%166%172$1@2%166%174$0@2$2@3|@|@|@3%101%101%83%39%85%26%110%167%178$0@2%169$1@3%167%169$1@2%178$0@3|@|@2%82%42%83%39%85%26%108%166%178$0@2%166%169$1@2$2@3%166%169$1@2%166%178$0@2$2@3|@|@|@3%101%101%87%41%85%26%110%167%178$0@2%172$1@3%167%172$1@2%178$0@3|@|@2%82%42%87%41%85%26%108%166%178$0@2%166%172$1@2$2@3%166%172$1@2%166%178$0@2$2@3|@|@|@3%101%101%85%40%85%26%110%167%178$0@2%174$1@3%167%174$1@2%178$0@3|@|@2%82%42%85%40%85%26%108%166%178$0@2%166%174$1@2$2@3%166%174$1@2%166%178$0@2$2@3|@|@|@3%101%101%83%39%83%24%110%167%176$0@2%169$1@3%167%169$1@2%176$0@3|@|@2%82%42%83%39%83%24%108%166%176$0@2%166%169$1@2$2@3%166%169$1@2%166%176$0@2$2@3|@|@|@3%101%101%87%41%83%24%110%167%176$0@2%172$1@3%167%172$1@2%176$0@3|@|@2%82%42%87%41%83%24%108%166%176$0@2%166%172$1@2$2@3%166%172$1@2%166%176$0@2$2@3|@|@|@3%101%101%85%40%83%24%110%167%176$0@2%174$1@3%167%174$1@2%176$0@3|@|@2%82%42%85%40%83%24%108%166%176$0@2%166%174$1@2$2@3%166%174$1@2%166%176$0@2$2@3|@|@|@3%101%85%40%83%24%110%167%176$0@2%178$1@3%167%178$1@2%176$0@3|@|@2%82%42%85%40%83%24%108%166%176$0@2%166%178$1@2$2@3%166%178$1@2%166%176$0@2$2@3|@|@|@11"])
  fun op otp_state_component_equality x = x
    val op otp_state_component_equality =
    ThmBind.DT(((("otp_tls",23),
                [("bool",[25,26,50,55,62,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3,11]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%93%58%93%59%105%113$1@$0@2%101%109%168$1@2%168$0@3%101%112%171$1@2%171$0@3%101%111%173$1@2%173$0@3%101%111%177$1@2%177$0@3%109%175$1@2%175$0@7|@|@"])
  fun op otp_state_updates_eq_literal x = x
    val op otp_state_updates_eq_literal =
    ThmBind.DT(((("otp_tls",24),
                [("bool",[25,26,55,180]),("combin",[12]),
                 ("otp_tls",[1,2,3,17])]),["DISK_THM"]),
               [ThmBind.read"%93%57%86%30%92%51%91%46%91%45%86%27%113%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2$5@6%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2%125@6|@|@|@|@|@|@"])
  fun op otp_state_literal_nchotomy x = x
    val op otp_state_literal_nchotomy =
    ThmBind.DT(((("otp_tls",25),
                [("bool",[25,26,50,55,57,62,142,180]),("combin",[12]),
                 ("ind_type",[33,34]),("otp_tls",[1,2,3,17]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%93%57%116%30%120%51%119%46%119%45%116%27%113$5@%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2%125@6|@|@|@|@|@|@"])
  fun op FORALL_otp_state x = x
    val op FORALL_otp_state =
    ThmBind.DT(((("otp_tls",26),
                [("bool",[25,26,35,50,55,57,62,142,180]),("combin",[12]),
                 ("ind_type",[33,34]),("otp_tls",[1,2,3,17]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%88%8%105%93%57$1$0@|@2%86%30%92%51%91%46%91%45%86%27$5%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2%125@6|@|@|@|@|@2|@"])
  fun op EXISTS_otp_state x = x
    val op EXISTS_otp_state =
    ThmBind.DT(((("otp_tls",27),
                [("bool",[25,26,50,55,57,62,142,180]),("combin",[12]),
                 ("ind_type",[33,34]),("otp_tls",[1,2,3,17]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%88%8%105%121%57$1$0@|@2%116%30%120%51%119%46%119%45%116%27$5%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2%125@6|@|@|@|@|@2|@"])
  fun op otp_state_literal_11 x = x
    val op otp_state_literal_11 =
    ThmBind.DT(((("otp_tls",28),
                [("combin",[12]),("otp_tls",[18,23])]),["DISK_THM"]),
               [ThmBind.read"%86%31%92%52%91%47%91%49%86%35%86%32%92%53%91%48%91%50%86%37%105%113%169%136$9@2%172%138$8@2%174%137$7@2%178%137$6@2%176%136$5@2%125@6%169%136$4@2%172%138$3@2%174%137$2@2%178%137$1@2%176%136$0@2%125@7%101%109$9@$4@2%101%112$8@$3@2%101%111$7@$2@2%101%111$6@$1@2%109$5@$0@6|@|@|@|@|@|@|@|@|@|@"])
  fun op datatype_otp_state x = x
    val op datatype_otp_state =
    ThmBind.DT(((("otp_tls",29),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%134%64%61@%1@%2@%3@%7@%4@2"])
  fun op otp_state_11 x = x
    val op otp_state_11 =
    ThmBind.DT(((("otp_tls",30),
                [("bool",[26,50,55,62,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%86%10%92%13%91%15%91%17%86%19%86%11%92%14%91%16%91%18%86%20%105%113%181$9@$8@$7@$6@$5@2%181$4@$3@$2@$1@$0@3%101%109$9@$4@2%101%112$8@$3@2%101%111$7@$2@2%101%111$6@$1@2%109$5@$0@6|@|@|@|@|@|@|@|@|@|@"])
  fun op otp_state_case_cong x = x
    val op otp_state_case_cong =
    ThmBind.DT(((("otp_tls",31),
                [("bool",[26,180]),("otp_tls",[1,2,3,4])]),["DISK_THM"]),
               [ThmBind.read"%93%5%93%6%84%25%115%101%113$2@$1@2%86%10%92%13%91%15%91%17%86%19%115%113$6@%181$4@$3@$2@$1@$0@3%104$5$4@$3@$2@$1@$0@2%29$4@$3@$2@$1@$0@3|@|@|@|@|@3%104%170$2@$0@2%170$1@%29@3|@|@|@"])
  fun op otp_state_nchotomy x = x
    val op otp_state_nchotomy =
    ThmBind.DT(((("otp_tls",32),
                [("bool",[26,180]),("otp_tls",[1,2,3])]),["DISK_THM"]),
               [ThmBind.read"%93%60%116%27%120%51%119%45%119%46%116%30%113$5@%181$4@$3@$2@$1@$0@2|@|@|@|@|@|@"])
  fun op otp_state_Axiom x = x
    val op otp_state_Axiom =
    ThmBind.DT(((("otp_tls",33),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("otp_tls",[1,2,3]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%84%25%117%38%86%10%92%13%91%15%91%17%86%19%104$5%181$4@$3@$2@$1@$0@3$6$4@$3@$2@$1@$0@2|@|@|@|@|@|@|@"])
  fun op otp_state_induction x = x
    val op otp_state_induction =
    ThmBind.DT(((("otp_tls",34),
                [("bool",[26]),("otp_tls",[1,2,3])]),["DISK_THM"]),
               [ThmBind.read"%88%8%115%86%27%92%51%91%45%91%46%86%30$5%181$4@$3@$2@$1@$0@2|@|@|@|@|@2%93%57$1$0@|@2|@"])

  val _ = DB.bindl "otp_tls"
  [("otp_state_TY_DEF",otp_state_TY_DEF,DB.Def),
   ("otp_state_case_def",otp_state_case_def,DB.Def),
   ("otp_state_size_def",otp_state_size_def,DB.Def),
   ("otp_state_Buffer",otp_state_Buffer,DB.Def),
   ("otp_state_CurrSeq",otp_state_CurrSeq,DB.Def),
   ("otp_state_In",otp_state_In,DB.Def),
   ("otp_state_Out",otp_state_Out,DB.Def),
   ("otp_state_Key",otp_state_Key,DB.Def),
   ("otp_state_Buffer_fupd",otp_state_Buffer_fupd,DB.Def),
   ("otp_state_CurrSeq_fupd",otp_state_CurrSeq_fupd,DB.Def),
   ("otp_state_In_fupd",otp_state_In_fupd,DB.Def),
   ("otp_state_Out_fupd",otp_state_Out_fupd,DB.Def),
   ("otp_state_Key_fupd",otp_state_Key_fupd,DB.Def),
   ("max_seq_def",max_seq_def,DB.Def), ("buffer_def",buffer_def,DB.Def),
   ("shift_buffer_def",shift_buffer_def,DB.Def),
   ("put_val_in_buf_def",put_val_in_buf_def,DB.Def),
   ("uart_read_def",uart_read_def,DB.Def), ("valid_def",valid_def,DB.Def),
   ("get_seq_no_def",get_seq_no_def,DB.Def),
   ("test_buffer_def",test_buffer_def,DB.Def),
   ("seq_in_order_def",seq_in_order_def,DB.Def),
   ("encrypt_def",encrypt_def,DB.Def),
   ("encrypt_buffer_def",encrypt_buffer_def,DB.Def),
   ("zero_datah_def",zero_datah_def,DB.Def),
   ("uart_write_buffer_def",uart_write_buffer_def,DB.Def),
   ("tls_otp_spec_def",tls_otp_spec_def,DB.Def),
   ("otp_state_accessors",otp_state_accessors,DB.Thm),
   ("otp_state_fn_updates",otp_state_fn_updates,DB.Thm),
   ("otp_state_accfupds",otp_state_accfupds,DB.Thm),
   ("otp_state_fupdfupds",otp_state_fupdfupds,DB.Thm),
   ("otp_state_fupdfupds_comp",otp_state_fupdfupds_comp,DB.Thm),
   ("otp_state_fupdcanon",otp_state_fupdcanon,DB.Thm),
   ("otp_state_fupdcanon_comp",otp_state_fupdcanon_comp,DB.Thm),
   ("otp_state_component_equality",otp_state_component_equality,DB.Thm),
   ("otp_state_updates_eq_literal",otp_state_updates_eq_literal,DB.Thm),
   ("otp_state_literal_nchotomy",otp_state_literal_nchotomy,DB.Thm),
   ("FORALL_otp_state",FORALL_otp_state,DB.Thm),
   ("EXISTS_otp_state",EXISTS_otp_state,DB.Thm),
   ("otp_state_literal_11",otp_state_literal_11,DB.Thm),
   ("datatype_otp_state",datatype_otp_state,DB.Thm),
   ("otp_state_11",otp_state_11,DB.Thm),
   ("otp_state_case_cong",otp_state_case_cong,DB.Thm),
   ("otp_state_nchotomy",otp_state_nchotomy,DB.Thm),
   ("otp_state_Axiom",otp_state_Axiom,DB.Thm),
   ("otp_state_induction",otp_state_induction,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "otp_tls",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "otp_tls.max_seq_def otp_tls.tls_otp_spec_def otp_tls.put_val_in_buf_def otp_tls.uart_read_def otp_tls.shift_buffer_def otp_tls.get_seq_no_def otp_tls.test_buffer_def otp_tls.seq_in_order_def otp_tls.encrypt_def otp_tls.encrypt_buffer_def otp_tls.zero_datah_def otp_tls.valid_def otp_tls.uart_write_buffer_def otp_tls.buffer_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "otp_tls",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "TYA7.otp_tls,4.byte3.%74TYA7.otp_tls,16.otp_input_stream3.%76TYA7.otp_tls,14.otp_key_stream3.%75TYA7.otp_tls,17.otp_output_stream3.%76TYA7.otp_tls,10.otp_buffer3.%75NTY7.otp_tls,9.otp_state"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "otp_tls",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO20.recordtype.otp_state4.%181OO14.otp_state_CASE4.%170OO14.otp_state_size4.%179OO16.otp_state_Buffer4.%168OO17.otp_state_CurrSeq4.%171OO12.otp_state_In4.%173OO13.otp_state_Out4.%177OO13.otp_state_Key4.%175OO21.otp_state_Buffer_fupd4.%169OO22.otp_state_CurrSeq_fupd4.%172OO17.otp_state_In_fupd4.%174OO18.otp_state_Out_fupd4.%178OO18.otp_state_Key_fupd4.%176OO22. _ record selectBuffer11.%63%168$0@|OO23. _ record selectCurrSeq11.%63%171$0@|OO18. _ record selectIn11.%63%173$0@|OO19. _ record selectOut11.%63%177$0@|OO19. _ record selectKey11.%63%175$0@|OO11.Buffer_fupd4.%169OO12.CurrSeq_fupd4.%172OO7.In_fupd4.%174OO8.Out_fupd4.%178OO8.Key_fupd4.%176OO23. _ record fupdateBuffer18.%24%77%169$1@$0@||OO24. _ record fupdateCurrSeq18.%28%77%172$1@$0@||OO19. _ record fupdateIn18.%26%77%174$1@$0@||OO20. _ record fupdateOut18.%26%77%178$1@$0@||OO20. _ record fupdateKey18.%24%77%176$1@$0@||OO9.otp_state4.%181OO4.case4.%170OO7.max_seq4.%160OO6.buffer4.%153OO12.shift_buffer4.%183OO14.put_val_in_buf4.%180OO9.uart_read4.%186OO5.valid4.%189OO10.get_seq_no4.%157OO11.test_buffer4.%184OO12.seq_in_order4.%182OO7.encrypt4.%154OO14.encrypt_buffer4.%156OO10.zero_datah4.%194OO17.uart_write_buffer4.%188OO12.tls_otp_spec4.%185"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val otp_tls_grammars = merge_grammars ["words"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="otp_tls"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val otp_tls_grammars = 
    Portable.## (addtyUDs,addtmUDs) otp_tls_grammars
  val _ = Parse.grammarDB_insert("otp_tls",otp_tls_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG otp_state_Axiom,
           case_def=otp_state_case_def,
           case_cong=otp_state_case_cong,
           induction=ORIG otp_state_induction,
           nchotomy=otp_state_nchotomy,
           size=SOME(Parse.Term`(otp_tls$otp_state_size) :otp_tls$otp_state -> num$num`,
                     ORIG otp_state_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME otp_state_11,
           distinct=NONE,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[("Buffer",(T"num" "num" [] -->
            T"fcp" "cart"
             [bool,
              T"fcp" "bit0"
               [T"fcp" "bit0"
                 [T"fcp" "bit0" [T"one" "one" []]]]])),
 ("CurrSeq",T"num" "num" []),
 ("In",T"list" "list"
        [T"fcp" "cart"
          [bool,
           T"fcp" "bit0"
            [T"fcp" "bit0"
              [T"fcp" "bit0" [T"one" "one" []]]]]]),
 ("Out",T"list" "list"
         [T"fcp" "cart"
           [bool,
            T"fcp" "bit0"
             [T"fcp" "bit0"
               [T"fcp" "bit0" [T"one" "one" []]]]]]),
 ("Key",(T"num" "num" [] -->
         T"fcp" "cart"
          [bool,
           T"fcp" "bit0"
            [T"fcp" "bit0"
              [T"fcp" "bit0" [T"one" "one" []]]]]))] end,
           accessors=Drule.CONJUNCTS otp_state_accessors,
           updates=Drule.CONJUNCTS otp_state_fn_updates,
           recognizers=[],
           destructors=[]}
        val tyinfo0 = RecordType.update_tyinfo NONE [otp_state_accessors, otp_state_updates_eq_literal, otp_state_accfupds, otp_state_fupdfupds, otp_state_literal_11, otp_state_fupdfupds_comp, otp_state_fupdcanon, otp_state_fupdcanon_comp] tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];

val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "otp_tls"
end
