----------------------------------------------------------------------
-- Formal Specification of the ARMv6-M instruction set architecture --
-- (c) Anthony Fox, University of Cambridge                         --
----------------------------------------------------------------------

-- Instruction semantics

-- ~~~~~~~~~~~~~~~~~~~
-- T: B<c> <label>
-- ~~~~~~~~~~~~~~~~~~~

define Branch > BranchTarget
   ( imm32 :: bits(32) )
   =
{
   BranchWritePC (PC + imm32);
   count <- count + 3
}

-- ~~~~~~~~~~~~~~~
-- T: BX <Rm>
-- ~~~~~~~~~~~~~~~

define Branch > BranchExchange
   ( m :: reg )
   =
{
   BXWritePC (R (m));
   count <- count + 3
}

-- ~~~~~~~~~~~~~~~~~~~
-- T2: BL <label>
-- ~~~~~~~~~~~~~~~~~~~

define Branch > BranchLinkImmediate
   ( imm32 :: bits(32) )
   =
{  next_instr_addr = PC;
   LR <- next_instr_addr<31:1> : '1';
   BranchWritePC (PC + imm32);
   count <- count + 4
}

-- ~~~~~~~~~~~~~~~~
-- T: BLX <Rm>
-- ~~~~~~~~~~~~~~~~

define Branch > BranchLinkExchangeRegister
   ( m :: reg )
   =
{  target = R(m);
   next_instr_addr = PC - 2;
   LR <- next_instr_addr<31:1> : '1';
   BLXWritePC (target);
   count <- count + 3
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- For opc in {AND,EOR,ADC,SBC,ORR,BIC,ADD,SUB,RSB}
-- T: <opc>{S} <Rd>, <Rn>, #<const>
-- T: <opc>{S} <Rd>, <Rn>, <Rm>
--
-- For opc in {MOV,MVN}
-- T: <opc>{S} <Rd>, #<const>
-- T: <opc>{S} <Rd>, <Rm>
--
-- T: CMP <Rn>, #<const>
-- For opc in {TST,CMN,CMP}
-- T: <opc> <Rn>, <Rm>
--
-- For opc in {LSL,LSR,ASR,ROR}
-- T: <opc>S <Rd>, <Rm>, #<const>
-- T: <opc>S <Rd>, <Rn>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

unit DataProcessing
   ( opc      :: bits(4),
     setflags :: bool,
     d        :: reg,
     n        :: reg,
     imm32    :: word,
     C        :: bool )
   =
{  rn = if opc == 0b1101 or -- MOV
           opc == 0b1111 -- MVN
           then 0
        else if opc in set {0b0100, 0b0010} and n == 15 and not setflags
           then Align (PC, 4)
        else R(n);

   result, carry, overflow = DataProcessingALU (opc, rn, imm32, C);

   when opc<3:2> != 0b10 do
      R(d) <- result;

   when setflags do
   {  PSR.N <- result<31>;
      PSR.Z <- result == 0;
      PSR.C <- carry;
      when ArithmeticOpcode (opc) do
         PSR.V <- overflow
   };

   IncPC();
   count <- count + 1
}

unit DataProcessingPC
   ( opc   :: bits(4),
     n     :: reg,
     imm32 :: word,
     C     :: bool )
   =
{  rn = if opc == '1101'
           then 0
        else if n == 15
           then PC
        else R(n);

   result, _ = DataProcessingALU (opc, rn, imm32, C);

   ALUWritePC (result);
   count <- count + 3
}

-- - - - - - - - - -
-- Immediate Operand
-- - - - - - - - - -

define Data > Move
   ( d     :: reg,
     imm32 :: bits(32) )
   =
   DataProcessing ('1101', true, d, 15, imm32, PSR.C)

define Data > CompareImmediate
   ( n     :: reg,
     imm32 :: bits(32) )
   =
   DataProcessing ('1010', true, UNKNOWN, n, imm32, PSR.C)

define Data > ArithLogicImmediate
   ( opc      :: bits(4),
     setflags :: bool,
     d        :: reg,
     n        :: reg,
     imm32    :: bits(32) )
   =
   DataProcessing (opc, setflags, d, n, imm32, PSR.C)

-- - - - - - - - - -
-- Register Operand
-- - - - - - - - - -

unit doRegister
   ( opc      :: bits(4),
     setflags :: bool,
     d        :: reg,
     n        :: reg,
     m        :: reg,
     shift_t  :: SRType,
     shift_n  :: nat )
   =
{  shifted, carry = Shift_C (R(m), shift_t, shift_n, PSR.C);
   carry = if ArithmeticOpcode (opc) then PSR.C else carry;
   if d == 15 then
      DataProcessingPC (opc, n, shifted, carry)
   else
      DataProcessing (opc, setflags, d, n, shifted, carry)
}

define Data > Register
   ( opc      :: bits(4),
     setflags :: bool,
     d        :: reg,
     n        :: reg,
     m        :: reg )
   =
   doRegister (opc, setflags, d, n, m, SRType_LSL, 0)

-- - - - - - - - - - - - - - - -
-- TST, CMP, CMN (register)
-- - - - - - - - - - - - - - - -

define Data > TestCompareRegister
   ( opc      :: bits(2),
     n        :: reg,
     m        :: reg )
   =
   doRegister ('10' : opc, true, 0, n, m, SRType_LSL, 0)

-- - - - - - - - - - - - - - - - - - - - - - - - - - -
-- MOV, MVN (register), LSL, LSR, ASR, ROR (immediate)
-- - - - - - - - - - - - - - - - - - - - - - - - - - -

define Data > ShiftImmediate
   ( negate   :: bool,
     setflags :: bool,
     d        :: reg,
     m        :: reg,
     shift_t  :: SRType,
     shift_n  :: nat )
   =
   if negate then
      doRegister (0b1111, setflags, d, 15, m, shift_t, shift_n)
   else
      doRegister (0b1101, setflags, d, UNKNOWN, m, shift_t, shift_n)

-- - - - - - - - - - - - - - - - - -
-- Register-Shifted-Register Operand
-- LSL, LSR, ASR, ROR (register)
-- - - - - - - - - - - - - - - - - -

define Data > ShiftRegister
   ( d       :: reg,
     n       :: reg,
     shift_t :: SRType,
     m       :: reg )
   =
{  shift_n = [R(m)<7:0>];
   shifted, carry = Shift_C (R(n), shift_t, shift_n, PSR.C);
   DataProcessing (0b1101, true, d, UNKNOWN, shifted, carry)
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: MULS <Rdm>, <Rn>, <Rdm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Multiply > Multiply32
   ( d :: reg,
     n :: reg,
     m :: reg )
   =
{  result = R(n) * R(m);
   R(d) <- result;
   PSR.N <- result<31>;
   PSR.Z <- result == 0;
   IncPC();
   count <- count + 1 -- could be 32 depending on implementation
}

--------------------------
-- Basic SIMD Instructions
--------------------------

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: SXTB <Rd>, <Rm>
-- T: UXTB <Rd>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Media > ExtendByte
   ( unsigned :: bool,
     d        :: reg,
     m        :: reg )
   =
{
   R(d) <- Extend (unsigned, R(m)<7:0>);
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: SXTH <Rd>, <Rm>
-- T: UXTH <Rd>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Media > ExtendHalfword
   ( unsigned :: bool,
     d        :: reg,
     m        :: reg )
   =
{
   R(d) <- Extend (unsigned, R(m)<15:0>);
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~
-- T: REV <Rd>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~

define Media > ByteReverse
   ( d :: reg,
     m :: reg )
   =
{  Rm = R(m);
   R(d) <- Rm<7:0> : Rm<15:8> : Rm<23:16> : Rm<31:24>;
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: REV16 <Rd>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

define Media > ByteReversePackedHalfword
   ( d :: reg,
     m :: reg )
   =
{  Rm = R(m);
   R(d) <- Rm<23:16> : Rm<31:24> : Rm<7:0> : Rm<15:8>;
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: REVSH <Rd>, <Rm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

define Media > ByteReverseSignedHalfword
   ( d :: reg,
     m :: reg )
   =
{  Rm = R(m);
   R(d) <- SignExtend (Rm<7:0>) : Rm<15:8>;
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: LDR <Rt>, [<Rn>{, #<imm>}]
-- T: LDR <Rt>, [SP{, #<imm>}]
-- T: LDR <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

construct offset
{
   register_form :: reg
   immediate_form :: word
}

define Load > LoadWord
   ( t :: reg,
     n :: reg,
     m :: offset )
   =
{  offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   data = MemU(address, 4);
   R(t) <- data;
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: LDR <Rt>, <label>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

define Load > LoadLiteral
   ( t     :: reg,
     imm32 :: word )
   =
{  base = Align (PC, 4);
   address = base + imm32;
   R(t) <- MemU(address, 4);
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: LDRB  <Rt>, [<Rn>{, #<imm>}]
-- T: LDRB  <Rt>, [SP{, #<imm>}]
-- T: LDRB  <Rt>, [<Rn>, <Rm>]
-- T: LDRSB <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Load > LoadByte
   ( unsigned :: bool,
     t        :: reg,
     n        :: reg,
     m        :: offset )
   =
{  offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   data`8 = MemU(address, 1);
   R(t) <- Extend (unsigned, data);
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: LDR{S}H <Rt>, [<Rn>{, #<imm>}]
-- T: LDR{S}H <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Load > LoadHalf
   ( unsigned :: bool,
     t        :: reg,
     n        :: reg,
     m        :: offset )
   =
{ offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   data`16 = MemU(address, 2);
   R(t) <- Extend (unsigned, data);
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: POP <registers>
-- T: LDM <Rn>!, <registers>   (<Rn> not included in <registers>)
-- T: LDM <Rn>, <registers>    (<Rn> included in <registers>)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Load > LoadMultiple
   ( wback     :: bool,
     n         :: reg,
     registers :: bits(9) )
   =
{  Rn = R(n);
   bitcount = BitCount (registers);
   var address = Rn;
   for i in 0 .. 7 do
      when registers<i> do
      {  R([i]) <- MemA(address, 4);
         address <- address + 4
      };
   if registers<8> then
   {
      LoadWritePC (MemA(address, 4));
      count <- count + bitcount + 4
   }
   else
   {
      IncPC();
      count <- count + bitcount + 1
   };
   when wback and not registers<[n]> do
      R(n) <- Rn + 4 * [bitcount]
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: STR <Rt>, [<Rn>{, #<imm>}]
-- T: STR <Rt>, [SP{, #<imm>}]
-- T: STR <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > StoreWord
   ( t :: reg,
     n :: reg,
     m :: offset )
   =
{  offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   MemU(address,4) <- R(t);
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: STRB <Rt>, [<Rn>{, #<imm>}]
-- T: STRB <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > StoreByte
   ( t :: reg,
     n :: reg,
     m :: offset )
   =
{  offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   MemU(address,1) <- R(t)<7:0>;
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: STRH <Rt>, [<Rn>{, #<imm>}]
-- T: STRH <Rt>, [<Rn>, <Rm>]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > StoreHalf
   ( t :: reg,
     n :: reg,
     m :: offset )
   =
{  offset = match m
            { case register_form (m) => Shift (R(m), SRType_LSL, 0, PSR.C)
              case immediate_form (imm32) => imm32
            };
   address = R(n) + offset;
   MemU(address,2) <- R(t)<15:0>;
   IncPC();
   count <- count + 2
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: STM  <Rn>!, <registers>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > StoreMultiple
   ( n         :: reg,
     registers :: bits(8) )
   =
{  Rn = R(n);
   bitcount = BitCount (registers);
   lowest = LowestSetBit (registers);
   var address = Rn;
   for i in 0 .. 7 do
      when registers<[i]> do
      {  if [i] == n and i != lowest then
            MemA(address,4) <- UNKNOWN::word
         else
            MemA(address,4) <- R([i]);
         address <- address + 4
      };
   R(n) <- Rn + 4 * [bitcount];
   IncPC();
   count <- count + bitcount + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: PUSH <registers>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > Push
   ( registers :: bits(9) )
   =
{  sp = SP;
   bitcount = BitCount (registers);
   length = 4 * [bitcount];
   var address = sp - length;
   for i in 0 .. 8 do
      when registers<[i]> do
      {  MemA(address,4) <- if i == 8 then LR else R([i]);
         address <- address + 4
      };
   SP <- sp - length;
   IncPC();
   count <- count + bitcount + 1
}

{-
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: PUSH <registers>
-- T: STM  <Rn>!, <registers>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define Store > StoreMultiple
   ( increment :: bool,
     n         :: reg,
     registers :: bits(15) )
   =
{  Rn = R(n);
   bitcount = BitCount (registers);
   length = 4 * [bitcount];
   lowest = LowestSetBit (registers);
   var address = if increment then Rn else Rn - length;
   for i in 0 .. 14 do
      when registers<[i]> do
      {  if [i] == n and i != lowest then
            MemA(address,4) <- UNKNOWN::word
         else
            MemA(address,4) <- R([i]);
         address <- address + 4
      };
   R(n) <- if increment then Rn + length else Rn - length;
   IncPC();
   count <- count + bitcount + 1
}
-}

-- ~~~~~~~~~~~~~~~~
-- T: SVC {#}<imm>
-- ~~~~~~~~~~~~~~~~

define System > SupervisorCall
   ( imm32 :: word )
   =
{
   CallSupervisor();
   count <- count + UNKNOWN -- depends on core and debug configuration
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T: CPS<effect> i
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define System > ChangeProcessorState
   ( im :: bool )
   =
{  when CurrentModeIsPrivileged() do
      PRIMASK.PM <- im;
   IncPC();
   count <- count + 1
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T2: MRS <Rd>, <spec_reg>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define System > MoveToRegisterFromSpecial
   ( SYSm :: bits(8),
     d    :: reg )
   =
{  R(d) <- 0;
   match SYSm<7:3>
   {
      case '00000' =>
        {
           when SYSm<0> do
              R(d)<8:0> <- &PSR<8:0>;
           when SYSm<1> do
              R(d)<24> <- false;
           when not SYSm<2> do
              R(d)<31:27> <- &PSR<31:27>
        }
      case '00001' =>
        match SYSm<2:0>
        {
           case '000' => R(d) <- SP_main
           case '001' => R(d) <- SP_process
           case _ => nothing
        }
      case '00010' =>
           match SYSm<2:0>
           {
              case '000' => R(d)<0> <- PRIMASK.PM
              case '100' => R(d)<1:0> <- &CONTROL<1:0>
              case _ => nothing
           }
      case _ => nothing
   };
   IncPC();
   count <- count + 4
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- T2: MSR <spec_reg>, <Rn>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

define System > MoveToSpecialRegister
   ( SYSm :: bits(8),
     n    :: reg )
   =
{  Rn = R(n);
   match SYSm<7:3>
   {
      case '00000' =>
        when not SYSm<2> do &PSR<31:27> <- Rn<31:27>
      case '00001' =>
        when CurrentModeIsPrivileged() do
           match SYSm<2:0>
           {
              case '000' => SP_main <- Rn<31:2> : '00'
              case '001' => SP_process <- Rn<31:2> : '00'
              case _ => nothing
           }
      case '00010' =>
        when CurrentModeIsPrivileged() do
           match SYSm<2:0>
           {
              case '000' => PRIMASK.PM <- Rn<0>
              case '100' =>
                 when CurrentMode == Mode_Thread do
                 {
                    CONTROL.SPSEL <- Rn<1>;
                    CONTROL.nPRIV <- Rn<0>
                 }
              case _ => nothing
           }
      case _ => nothing
   };
   IncPC();
   count <- count + 4
}

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = Raise (HardFault)

-- All treated as NO-OPs.

define NoOperation() = { IncPC(); count <- count + 1 }

define Hint > Breakpoint (imm32::word) = { IncPC(); count <- count + UNKNOWN }
define Hint > DataMemoryBarrier (option::bits(4)) =
  { IncPC(); count <- count + 4 }
define Hint > DataSynchronizationBarrier (option::bits(4)) =
  { IncPC(); count <- count + 4 }
define Hint > InstructionSynchronizationBarrier (option::bits(4)) =
  { IncPC(); count <- count + 4 }
define Hint > SendEvent() = { IncPC(); count <- count + 1 }
define Hint > WaitForEvent() = { IncPC(); count <- count + 2 }
define Hint > WaitForInterrupt() = { IncPC(); count <- count + 2 }
define Hint > Yield() = { IncPC(); count <- count + 1 }
