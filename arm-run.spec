----------------------------------------------------------------------
-- Formal Specification of the ARMv6-M instruction set architecture --
-- (c) Anthony Fox, University of Cambridge                         --
----------------------------------------------------------------------

define Run

--------------------
-- Instruction fetch
--------------------

construct MachineCode {
   Thumb   :: half
   Thumb2  :: half * half
}

MachineCode Fetch =
{  fpc = REG(RName_PC);
   ireg = MemA (fpc, 2);
   if ireg<15:13> == 0b111 and ireg<12:11> != 0b00 then
      Thumb2 (ireg, MemA (fpc + 2, 2))
   else
      Thumb (ireg)
}

-----------------------
-- Instruction decoding
-----------------------

unit DECODE_UNPREDICTABLE (mc::MachineCode, s::string) =
   #UNPREDICTABLE
     ( "Decode " :
       match mc
       {
         case Thumb (opc) =>
            [[opc]::bool list] : "; Thumb; "
         case Thumb2 (opc1, opc2) =>
            [[opc1]::bool list] : ", " : [[opc2]::bool list] : "; Thumb2; "
       } : s )

pattern {
   imm2 ` 2
   imm3 ` 3
   imm4 ` 4
   imm5 ` 5
   imm6 ` 6
   imm7 ` 7
   imm8 ` 8
   imm11 ` 11
}

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
-- 16-bit Thumb Decoder
-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

instruction DecodeThumb (h::half) =
{  mc = Thumb (h);
   match h
   {
     -- 1 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ADDS <Rd>, <Rn>, <Rm>
     -- SUBS <Rd>, <Rn>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '000 11 0 : S : Rm`3 : Rn`3 : Rd`3' =>
        {  d = [Rd];
           n = [Rn];
           m = [Rm];
           setflags = true;
           opc = if S == 1 then 0b0010 else 0b0100;
           Data (Register (opc, setflags, d, n, m))
        }

     -- 2 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ADDS <Rd>, <Rn>, #<imm3>
     -- SUBS <Rd>, <Rn>, #<imm3>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '000 11 1 : S : imm3 : Rn`3 : Rd`3' =>
        {  d = [Rd];
           n = [Rn];
           setflags = true;
           imm32 = ZeroExtend (imm3);
           opc = if S == 1 then 0b0010 else 0b0100;
           Data (ArithLogicImmediate (opc, setflags, d, n, imm32))
        }

     -- 3 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- <opc>S <Rd>, <Rm>, #<imm5>
     -- where <opc> in {LSL,LSR,ASR}
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '000 : opc`2 : imm5 : Rm`3 : Rd`3' =>
        {  d = [Rd];
           m = [Rm];
           setflags = true;
           shift_t, shift_n = DecodeImmShift (opc, imm5);
           Data (ShiftImmediate (false, setflags, d, m, shift_t, shift_n))
        }

     -- 4 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- MOVS <Rd>, #<imm8>  (Outside IT block)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '001 00 : Rd`3 : imm8' =>
        {  d = [Rd];
           imm32 = ZeroExtend (imm8);
           Data (Move (d, imm32))
        }

     -- 5 ~~~~~~~~~~~~~~~~~~
     -- CMP <Rn>, #<imm8>
     -- ~~~~~~~~~~~~~~~~~~~~
     case '001 01 : Rn`3 : imm8' =>
        {  n = [Rn];
           imm32 = ZeroExtend (imm8);
           Data (CompareImmediate (n, imm32))
        }

     -- 6 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ADDS <Rdn>, #<imm8>
     -- SUBS <Rdn>, #<imm8>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '001 1 : S : Rdn`3 : imm8' =>
        {  d = [Rdn];
           n = d;
           setflags = true;
           imm32 = ZeroExtend (imm8);
           opc = if S == 1 then 0b0010 else 0b0100;
           Data (ArithLogicImmediate (opc, setflags, d, n, imm32))
        }

     -- 7 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- <opc>S <Rdn>, <Rm>
     -- where <opc> in AND, EOR, ADC, SBC, ORR, BIC, LSL, LSR, ASR, ROR
     --
     -- <opc>S   <Rn>, <Rm>
     -- where <opc> in TST, CMP, CMN
     --
     -- RSBS <Rd>, <Rn>, #0
     -- MULS <Rdm>, <Rm>
     -- MVNS <Rd>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010000 : opc`4 : Rx`3 : Ry`3' =>
        match opc
        { case '0000' or '0001' or '0101' or '0110' or '1100' or '1110' =>
          -- AND, EOR, ADC, SBC, ORR, BIC
            {  d = [Ry];
               n = d;
               m = [Rx];
               setflags = true;
               Data (Register (opc, setflags, d, n, m))
            }
          case '0010' or '0011' or '0100' =>
          -- LSL, LSR, ASR
            {  d = [Ry];
               n = d;
               m = [Rx];
               shift_t = DecodeRegShift ([opc - 2]);
               Data (ShiftRegister (d, n, shift_t, m))
            }
          case '0111' =>
          -- ROR
            {  d = [Ry];
               n = d;
               m = [Rx];
               Data (ShiftRegister (d, n, SRType_ROR, m))
            }
          case '1000' or '1010' or '1011' =>
          -- TST, CMP, CMN
            {  n = [Ry];
               m = [Rx];
               Data (TestCompareRegister (opc<1:0>, n, m))
            }
          case '1001' =>
          -- RSB
            {  d = [Ry];
               n = [Rx];
               setflags = true;
               Data (ArithLogicImmediate (0b0011, setflags, d, n, 0))
            }
          case '1101' =>
          -- MUL
            {  d = [Ry];
               n = [Rx];
               m = d;
               Multiply (Multiply32 (d, n, m))
            }
          case '1111' =>
          -- MVN
            {  d = [Ry];
               m = [Rx];
               setflags = true;
               shift_t, shift_n = SRType_LSL, 0;
               Data (ShiftImmediate (true, setflags, d, m, shift_t, shift_n))
            }
        }

     -- 8 ~~~~~~~~~~~~~~~~
     -- ADD <Rdn>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~
     case '010001 00 : DN : Rm : Rdn`3' =>
        {  d = DN : Rdn;
           n = d;
           when n == 15 and Rm == 15 do
              DECODE_UNPREDICTABLE (mc, "ADD");
           setflags = false;
           Data (Register (0b0100, setflags, d, n, Rm))
        }

     -- 9 ~~~~~~~~~~~~~~~
     -- CMP <Rn>, <Rm>
     -- ~~~~~~~~~~~~~~~~~
     case '010001 01 : N : Rm : Rn`3' =>
        {  n = N : Rn;
           when n <+ 8 and Rm <+ 8 or n == 15 or Rm == 15 do
              DECODE_UNPREDICTABLE (mc, "CMP");
           Data (TestCompareRegister ('10', n, Rm))
        }

     -- 10 ~~~~~~~~~~~~~~~
     -- MOV <Rd>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~
     case '010001 10 : D : Rm : Rd`3' =>
        {  d = D : Rd;
           setflags = false;
           shift_t, shift_n = SRType_LSL, 0;
           Data (ShiftImmediate (false, setflags, d, Rm, shift_t, shift_n))
        }

     -- 11 ~~~~~~~~
     -- BX <Rm>
     -- ~~~~~~~~~~~
     case '010001 11 0 : Rm : (000)' =>
        Branch (BranchExchange (Rm))

     -- 12 ~~~~~~~~
     -- BLX <Rm>
     -- ~~~~~~~~~~~
     case '010001 11 1 : Rm : (000)' =>
        Branch (BranchLinkExchangeRegister (Rm))

     -- 13 ~~~~~~~~~~~~~~~~~
     -- LDR <Rt>, <label>
     -- ~~~~~~~~~~~~~~~~~~~~
     case '01001 : Rt`3 : imm8' =>
        {  imm32 = ZeroExtend (imm8 : '00');
           Load (LoadLiteral ([Rt], imm32))
        }

     -- 14 ~~~~~~~~~~~~~~~~~~~~~~~~
     -- STR   <Rt>, [<Rn>, <Rm>]
     -- STRH  <Rt>, [<Rn>, <Rm>]
     -- STRB  <Rt>, [<Rn>, <Rm>]
     -- LDRSB <Rt>, [<Rn>, <Rm>]
     -- LDR   <Rt>, [<Rn>, <Rm>]
     -- LDRH  <Rt>, [<Rn>, <Rm>]
     -- LDRB  <Rt>, [<Rn>, <Rm>]
     -- LDRSH <Rt>, [<Rn>, <Rm>]
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '0101 : opc`3 : Rm`3 : Rn`3 : Rt`3' =>
        {  m = register_form ([Rm]);
           match opc
           { case '000' => Store (StoreWord ([Rt], [Rn], m))
             case '001' => Store (StoreHalf ([Rt], [Rn], m))
             case '010' => Store (StoreByte ([Rt], [Rn], m))
             case '011' => Load (LoadByte (false, [Rt], [Rn], m))
             case '100' => Load (LoadWord ([Rt], [Rn], m))
             case '101' => Load (LoadHalf (true, [Rt], [Rn], m))
             case '110' => Load (LoadByte (true, [Rt], [Rn], m))
             case '111' => Load (LoadHalf (false, [Rt], [Rn], m))
           }
        }

     -- 15 ~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- STR <Rt>, [<Rn>{, #<imm>}]
     -- LDR <Rt>, [<Rn>{, #<imm>}]
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '0110 : L : imm5 : Rn`3 : Rt`3' =>
        {  imm32 = ZeroExtend (imm5 : '00');
           m = immediate_form (imm32);
           if L == 1 then
              Load (LoadWord ([Rt], [Rn], m))
           else
              Store (StoreWord ([Rt], [Rn], m))
        }

     -- 16 ~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- STRB <Rt>, [<Rn>{, #<imm>}]
     -- LDRB <Rt>, [<Rn>{, #<imm>}]
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '0111 : L : imm5 : Rn`3 : Rt`3' =>
        {  imm32 = ZeroExtend (imm5);
           m = immediate_form (imm32);
           if L == 1 then
              Load (LoadByte (true, [Rt], [Rn], m))
           else
              Store (StoreByte ([Rt], [Rn], m))
        }

     -- 17 ~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- STRH <Rt>, [<Rn>{, #<imm>}]
     -- LDRH <Rt>, [<Rn>{, #<imm>}]
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '1000 : L : imm5 : Rn`3 : Rt`3' =>
        {  imm32 = ZeroExtend (imm5 : '0');
           m = immediate_form (imm32);
           if L == 1 then
              Load (LoadHalf (true, [Rt], [Rn], m))
           else
              Store (StoreHalf ([Rt], [Rn], m))
        }

     -- 18 ~~~~~~~~~~~~~~~~~~~~~~
     -- STR <Rt>, [SP, #<imm>]
     -- LDR <Rt>, [SP, #<imm>]
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~
     case '1001 : L : Rt`3 : imm8' =>
        {  imm32 = ZeroExtend (imm8 : '00');
           m = immediate_form (imm32);
           if L == 1 then
              Load (LoadWord ([Rt], 13, m))
           else
              Store (StoreWord ([Rt], 13, m))
        }

     -- 19 ~~~~~~~~~~~~~~~~~~~~
     -- ADR <Rd>, <label>
     -- ADD <Rd>, SP, #<imm>
     -- ~~~~~~~~~~~~~~~~~~~~~~~
     case '1010 : S : Rd`3 : imm8' =>
        {  imm32 = ZeroExtend (imm8 : '00');
           Rn = if S == 1 then 13 else 15;
           Data (ArithLogicImmediate (0b0100, false, [Rd], Rn, imm32))
        }

     -- 20 ~~~~~~~~~~~~~~~~~~
     -- ADD SP, SP, #<imm>
     -- SUB SP, SP, #<imm>
     -- ~~~~~~~~~~~~~~~~~~~~~
     case '1011 0000 : S : imm7' =>
        {  imm32 = ZeroExtend (imm7 : '00');
           opc = if S == 1 then 0b0010 else 0b0100;
           Data (ArithLogicImmediate (opc, false, 13, 13, imm32))
        }

     -- 21 ~~~~~~~~~~~~~~~
     -- SXTH <Rd>, <Rm>
     -- UXTH <Rd>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~
     case '1011 0010 : U : 0 : Rm`3 : Rd`3' =>
        {  unsigned = U == 1;
           Media (ExtendHalfword (unsigned, [Rd], [Rm]))
        }

     -- 22 ~~~~~~~~~~~~~~~
     -- SXTB <Rd>, <Rm>
     -- UXTB <Rd>, <Rm>
     -- ~~~~~~~~~~~~~~~~~~
     case '1011 0010 : U : 1 : Rm`3 : Rd`3' =>
        {  unsigned = U == 1;
           Media (ExtendByte (unsigned, [Rd], [Rm]))
        }

     -- 23 ~~~~~~~~~~~~~~~~
     -- PUSH <registers>
     -- ~~~~~~~~~~~~~~~~~~~
     case '1011 010 : registers`9' =>
        {  when BitCount (registers) < 1 do
              DECODE_UNPREDICTABLE (mc, "Push");
           Store (Push (registers)) -- registers<8> represents LR
        }

     -- 24 ~~~~~~~~~~~~~~~~~
     -- CPS<effect> i
     -- ~~~~~~~~~~~~~~~~~~~~
     case '1011 0110 011 : im : (0010)' =>
        System (ChangeProcessorState ([im]))

     -- 25 ~~~~~~~~~~~~~~~~
     -- REV   <Rd>, <Rn>
     -- REV16 <Rd>, <Rn>
     -- REVSH <Rd>, <Rn>
     -- ~~~~~~~~~~~~~~~~~~~
     case '1011 1010 : opc`2 : Rm`3 : Rd`3' =>
        match opc
        { case '00' => Media (ByteReverse ([Rd], [Rm]))
          case '01' => Media (ByteReversePackedHalfword ([Rd], [Rm]))
          case '11' => Media (ByteReverseSignedHalfword ([Rd], [Rm]))
          case _    => Undefined (0)
        }

     -- 26 ~~~~~~~~~~~~~~~
     -- POP <registers>
     -- ~~~~~~~~~~~~~~~~~~
     case '1011 110 : registers`9' =>
        {  when BitCount (registers) < 1 do
              DECODE_UNPREDICTABLE (mc, "POP");
           wback = true;
           Load (LoadMultiple (wback, 13, registers)) -- registers<8> is for PC
        }

     -- 27 ~~~~~~~~
     -- BKPT #<imm>
     -- ~~~~~~~~~~~
     case '1011 1110 : imm8' =>
        {  imm32 = ZeroExtend (imm8);
           Hint (Breakpoint (imm32))
        }

     -- 28 ~~~~~
     -- NOP
     -- YIELD
     -- WFE
     -- WFI
     -- SEV
     -- ~~~~~~~~
     case '1011 1111 : op`4 : 0000' =>
        match op
        {
           case '0001' => Hint (Yield())
           case '0010' => Hint (WaitForEvent())
           case '0011' => Hint (WaitForInterrupt())
           case '0100' => Hint (SendEvent())
           case _          => NoOperation()
        }

     -- 29 ~~~~~~~~~~~~~~~~~~~~~~
     -- STM <Rn>!, <registers>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~
     case '1100 0 : Rn`3 : registers`8' =>
        {  when BitCount (registers) < 1 do
              DECODE_UNPREDICTABLE (mc, "StoreMultiple");
           Store (StoreMultiple ([Rn], registers))
        }

     -- 30 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- LDM <Rn>!, <registers>  (<Rn> not included in <registers>)
     -- LDM <Rn>, <registers>   (<Rn> included in <registers>)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '1100 1 : Rn`3 : register_list`8' =>
        {  registers = [register_list];
           when BitCount (registers) < 1 do
              DECODE_UNPREDICTABLE (mc, "LoadMultiple");
           wback = not registers<[Rn]>;
           Load (LoadMultiple (wback, [Rn], registers))
        }

     -- 31 ~~~~~~~~~~~
     -- UDF #<imm8>
     -- ~~~~~~~~~~~~~~
     case '1101 1110 : imm8' =>
        {  imm32 = ZeroExtend (imm8);
           Undefined (imm32)
        }

     -- 32 ~~~~~~~~~~~~~
     -- SVC {#}<imm>
     -- ~~~~~~~~~~~~~~~~
     case '1101 1111 : imm8' =>
        System (SupervisorCall (ZeroExtend (imm8)))

     -- 33 ~~~~~~~~~
     -- B<c> <label>
     -- ~~~~~~~~~~~~
     case '1101 : cond : imm8' =>
        if ConditionPassed (cond) then
           {  imm32 = SignExtend (imm8 : '0');
              Branch (BranchTarget (imm32))
           }
        else
           NoOperation()

     -- 34 ~~~~~~~~~
     -- B <label>
     -- ~~~~~~~~~~~~
     case '11100 : imm11' =>
        {  imm32 = SignExtend (imm11 : '0');
           Branch (BranchTarget (imm32))
        }

     -- 35 ~~~~~~~~~~~~
     -- Everything else
     -- ~~~~~~~~~~~~~~~

     case _ => Undefined (0)
   }
}

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
-- 2 * 16-bit Thumb-2 Decoder
-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

instruction DecodeThumb2 (h::half * half) =
{  mc = Thumb2 (h);
   match h
   {

     -- 1 ~~~~~~~~~~~~~~~~~~~~~
     -- MSR <spec_reg>, <Rn>
     -- ~~~~~~~~~~~~~~~~~~~~~~~
     case '11110 011100 : (0) : Rn', '10 (0) 0 (1000) SYSm' =>
        {  when Rn in set {13,15} or
                SYSm notin set {0,1,2,3,5,6,7,8,9,16,17,18,19,20} do
              DECODE_UNPREDICTABLE (mc, "MoveToSpecialRegister");
           System (MoveToSpecialRegister (SYSm, Rn))
        }

     -- 2 ~~~~~~~~~~~~~
     -- DSB <option>
     -- DMB <option>
     -- ISB <option>
     -- ~~~~~~~~~~~~~~~
     case '11110011101 1 (1111)', '10 (0) 0 (1111) : op`4 : option`4' =>
        {  match op
           { case '0100' => Hint (DataSynchronizationBarrier (option))
             case '0101' => Hint (DataMemoryBarrier (option))
             case '0110' => Hint (InstructionSynchronizationBarrier (option))
             case _ => Undefined (0)
           }
        }

     -- 3 ~~~~~~~~~~~~~~~~~~~~~~~
     -- MRS <Rd>, <banked_reg>
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~
     case '11110 011111 : (01111)', '10 (0) 0 : Rd : SYSm' =>
        {  when Rd in set {13,15} or
                SYSm notin set {0,1,2,3,5,6,7,8,9,16,17,18,19,20} do
              DECODE_UNPREDICTABLE (mc, "MoveToRegisterFromSpecial");
           System (MoveToRegisterFromSpecial (SYSm, Rd))
        }

     -- 4 ~~~~~~~~~~~~~~
     -- UDF.W <imm16>
     -- ~~~~~~~~~~~~~~~~
     case '11110 1111111 : imm4', '1010 : imm12' =>
        {  imm32 = ZeroExtend (imm4 : imm12);
           Undefined (imm32)
        }

     -- 5 ~~~~~~~~~~~~
     -- BL <label>
     -- ~~~~~~~~~~~~~~
     case '11110 : S`1 : imm10', '11 : J1`1 : 1 : J2`1 : imm11' =>
        {  I1 = ~(J1 ?? S);
           I2 = ~(J2 ?? S);
           imm32 = SignExtend (S : I1 : I2 : imm10 : imm11 : '0');
           Branch (BranchLinkImmediate (imm32))
        }

     -- 7 ~~~~~~~~~~~~~
     -- Everything else
     -- ~~~~~~~~~~~~~~~

     case _ => Undefined (0)
   }
}

clear patterns

instruction Decode (mc::MachineCode) =
   match mc
   {
     case Thumb (h) => { pcinc <- 2; DecodeThumb (h) }
     case Thumb2 (hs) => { pcinc <- 4; DecodeThumb2 (hs) }
   }

------------
-- Top-level
------------

unit Next = Run (Decode (Fetch))
