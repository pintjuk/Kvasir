----------------------------------------------------------------------
-- Formal Specification of the ARMv6-M instruction set architecture --
-- (c) Anthony Fox, University of Cambridge                         --
----------------------------------------------------------------------

-- Preliminaries

-----------------------------------
-- Word sizes (32-bit architecture)
-----------------------------------

type reg  = bits(4)
type cond = bits(4)
type byte = bits(8)
type half = bits(16)
type word = bits(32)

---------------------------
-- Specification exceptions
---------------------------

exception ASSERT :: string
exception UNPREDICTABLE :: string

----------------------
-- Cycle counts
----------------------

declare count :: nat

----------------------
-- Some Core Registers
----------------------

register PRIMASK :: word {
   0: PM
}

register PSR :: word {
     31: N  -- Condition flag (Negative)
     30: Z  -- Condition flag (Zero)
     29: C  -- Condition flag (Carry)
     28: V  -- Condition flag (oVerflow)
     24: T
    5-0: ExceptionNumber
}

register CONTROL :: bits(3) {
   1: SPSEL
   0: nPRIV
}

declare {
   PRIMASK :: PRIMASK
   PSR :: PSR
   CONTROL :: CONTROL
}

---------------------------------
-- Memory mapped system registers
---------------------------------

-- Vecror table offset register. Top bits of 0xE000ED08.

declare VTOR :: word

-- Application Interrupt and Reset Control Register

register AIRCR :: word { -- location 0xE000ED0C
  31-16: VECTKEY
     15: ENDIANNESS
      2: SYSRESETREQ
      1: VECTCLRACTIVE
}

declare AIRCR :: AIRCR

-- Configuration and Control Register

register CCR :: word { -- location 0xE000ED14
   9: STKALIGN
   3: UNALIGN_TRP
}

declare CCR :: CCR

-- System Handler Priority Registers

register SHPR2 :: word {
   31-30: PRI_11
}

declare SHPR2 :: SHPR2

register SHPR3 :: word {
   31-30: PRI_15
   23-22: PRI_14
}

declare SHPR3 :: SHPR3

-- Interrupt Priority Registers

register IPR :: word {
   31-30: PRI_N3
   23-22: PRI_N2
   15-14: PRI_N1
    7- 6: PRI_N0
}

declare NVIC_IPR :: bits(3) -> IPR

------------------------
-- Mode/state operations
------------------------

int ProcessorID() = return 0

-- Conditional instructions

bool ConditionPassed(cond::cond) =
{
   -- Evaluate base condition
   result = match cond<3:1>
            {  case '000' => PSR.Z                         -- EQ or NE
               case '001' => PSR.C                         -- CS or CC
               case '010' => PSR.N                         -- MI or PL
               case '011' => PSR.V                         -- VS or VC
               case '100' => PSR.C and not PSR.Z           -- HI or LS
               case '101' => PSR.N == PSR.V                -- GE or LT
               case '110' => PSR.N == PSR.V and not PSR.Z  -- GT or LE
               case '111' => true                          -- AL
            };

   -- Condition flag values in the set '111x' indicate the instruction is
   -- always run.  Otherwise, invert condition if necessary.
   if cond<0> and cond != 0b1111 then
      not result
   else
      result
}

---------------------------
-- ARM exceptions
---------------------------

construct Mode { Mode_Thread Mode_Handler }

construct ARM_Exception {
   Reset
   NMI
   HardFault
   SVCall
   PendSV
   SysTick
   ExternalInterrupt :: bits(6)
}

declare {
   CurrentMode :: Mode
   pending :: ARM_Exception option
   ExceptionActive :: bits(6) -> bool
}

-- This doesn't take account of exception priorities
unit Raise (e::ARM_Exception) = pending <- Some(e)

bool CurrentModeIsPrivileged() =
   CurrentMode == Mode_Handler or not CONTROL.nPRIV

-------------------------------------
-- General Purpose Registers (banked)
-------------------------------------

construct RName {
   RName_0   RName_1   RName_2  RName_3   RName_4  RName_5 RName_6
   RName_7   RName_8   RName_9  RName_10  RName_11 RName_12
   RName_SP_main RName_SP_process RName_LR  RName_PC
}

declare REG :: RName -> word

RName LookUpSP() = if CONTROL.SPSEL then RName_SP_process else RName_SP_main

component R (n::reg) :: word
{  value =
      if n == 15 then
         REG (RName_PC) + 4
      else if n == 14 then
         REG (RName_LR)
      else if n == 13 then
         REG (LookUpSP())
      else
         REG ([n])
   assign value =
      if n == 15 then
         #ASSERT ("n >= 0 and n <= 14")
      else if n == 14 then
         REG (RName_LR) <- value
      else if n == 13 then
         REG (LookUpSP()) <- value<31:2> : '00'
      else
         REG ([n]) <- value
}

component SP_main :: word {
   value = REG(RName_SP_main)
   assign value = REG(RName_SP_main) <- value
}

component SP_process :: word {
   value = REG(RName_SP_process)
   assign value = REG(RName_SP_process) <- value
}

component SP :: word { value = R(13) assign value = R(13) <- value }
component LR :: word { value = R(14) assign value = R(14) <- value }
component PC :: word { value = R(15) assign value = REG(RName_PC) <- value }

--------------
-- Main Memory
--------------

declare MEM :: word -> byte

bool list mem1 (address::word) = [MEM(address)]

component mem (address::word, size::nat) :: bool list
{  value =
      match size
      { case 1 => (mem1(address + 0))<7:0>
        case 2 => (mem1(address + 1) : mem1(address + 0))<15:0>
        case 4 => (mem1(address + 3) : mem1(address + 2) :
                   mem1(address + 1) : mem1(address + 0))<31:0>
        case _ => #ASSERT("mem: size in {1, 2, 4}")
      }
   assign value =
      match size
      { case 1 =>   MEM(address + 0) <- [value<7:0>]
        case 2 => { MEM(address + 0) <- [value<7:0>];
                    MEM(address + 1) <- [value<15:8>]
                  }
        case 4 => { MEM(address + 0) <- [value<7:0>];
                    MEM(address + 1) <- [value<15:8>];
                    MEM(address + 2) <- [value<23:16>];
                    MEM(address + 3) <- [value<31:24>]
                  }
        case _ => #ASSERT("mem: size in {1, 2, 4}")
      }
}

bool list BigEndianReverse (value::bool list, n::nat) =
   match n
   { case 1 => value<7:0>
     case 2 => value<7:0> : value<15:8>
     case 4 => value<7:0> : value<15:8> : value<23:16> : value<31:24>
     case _ => #ASSERT("BigEndianReverse: n in {1, 2, 4}")
   }

bits(N) Align (w::bits(N), n::nat) = return [n * ([w] div n)]

bool Aligned (w::bits(N), n::nat) = return ( w == Align (w, n) )

component MemA (address::word, size::nat) :: bits(N) with N in 8,16,32
{  value =
      -- Sort out aligment
      if not Aligned (address, size) then
      {
         Raise (HardFault);
         return UNKNOWN
      }
      else
      {
         -- Memory array access, and sort out endianness
         value = mem(address, size);
         return
           [if AIRCR.ENDIANNESS then
               BigEndianReverse (value, size)
            else
               value]
      }

   assign value =
      -- Sort out aligment
      if not Aligned (address, size) then
      {
         Raise (HardFault)
      }
      else -- Sort out endianness, then memory array access
         mem(address, size) <-
            if AIRCR.ENDIANNESS then
               BigEndianReverse ([value], size)
            else
               [value]
}

component MemU (address::word, size::nat) :: bits(N) with N in 8,16,32
{
   value = MemA(address, size)
   assign value = MemA(address, size) <- value
}

-------------------------------------
-- Branching and Exceptions (approx.)
-------------------------------------

bits(6) ExcNumber (e::ARM_Exception) =
   match e
   {
      case Reset => 1
      case NMI => 2
      case HardFault => 3
      case SVCall => 11
      case PendSV => 14
      case SysTick => 15
      case ExternalInterrupt (n) => 16 + n
   }

unit TakeReset () =
{
   vectortable = VTOR;
   for i in 0 .. 12 do R([i]) <- UNKNOWN;
   SP_main <- MemA(vectortable, 4);
   SP_process <- UNKNOWN : '00';
   LR <- UNKNOWN;
   PC <- MemA(vectortable + 4, 4);
   CurrentMode <- Mode_Thread;
   PSR <- UNKNOWN;
   PSR.ExceptionNumber <- 0x0;
   PRIMASK.PM <- false;
   CONTROL.SPSEL <- false;
   CONTROL.nPRIV <- false;
   for i in 0 .. 63 do ExceptionActive([i]) <- false
}

int ExceptionPriority (n::nat) =
   if n == 2 then
      -2
   else if n == 1 then
      -1
   else if n == 11 then
      [SHPR2.PRI_11]
   else if n == 14 then
      [SHPR3.PRI_14]
   else if n == 15 then
      [SHPR3.PRI_15]
   else if n >= 16 then
   {
      r = NVIC_IPR([(n - 16) div 4]);
      match [n mod 4]
      {
        case '00' => [r.PRI_N0]
        case '01' => [r.PRI_N1]
        case '10' => [r.PRI_N2]
        case '11' => [r.PRI_N3]
      }
   }
   else
      4

int ExecutionPriority () =
{
   var highestpri = 0i4;
   var boostedpri = 0i4;
   for i in 2 .. 48 do
      when ExceptionActive([i]) do
      {  p = ExceptionPriority(i);
         when p < highestpri do
            highestpri <- p
      };
   when PRIMASK.PM do
      boostedpri <- 0;
   return Min (boostedpri, highestpri)
}

-- This is a simplification. The return address could be PC - 4.
word ReturnAddress() = PC

unit PushStack () =
{
   var frameptralign;
   var frameptr;
   if CONTROL.SPSEL and CurrentMode == Mode_Thread then
   {
      frameptralign <- SP_process<2:2>;
      SP_process <- (SP_process - 0x20) && ~ZeroExtend ('100');
      frameptr <- SP_process
   }
   else
   {
      frameptralign <- SP_main<2:2>;
      SP_process <- (SP_main - 0x20) && ~ZeroExtend ('100');
      frameptr <- SP_main
   };
   MemA(frameptr, 4)      <- R(0);
   MemA(frameptr+0x4, 4)  <- R(1);
   MemA(frameptr+0x8, 4)  <- R(2);
   MemA(frameptr+0xC, 4)  <- R(3);
   MemA(frameptr+0x10, 4) <- R(12);
   MemA(frameptr+0x14, 4) <- LR;
   MemA(frameptr+0x14, 4) <- ReturnAddress();
   MemA(frameptr+0x1C, 4) <- &PSR<31:10> : frameptralign : &PSR<8:0>;
   if CurrentMode == Mode_Handler then
      LR <- 0xFFFFFFF1
   else if not CONTROL.SPSEL then
      LR <- 0xFFFFFFF9
   else
      LR <- 0xFFFFFFFD
}

unit ExceptionTaken (ExceptionNumber::bits(6)) =
{
   vectortable = VTOR;
   for i in 0 .. 3 do R([i]) <- UNKNOWN;
   R(12) <- UNKNOWN;
   PC <- MemA(vectortable + 4 * [ExceptionNumber], 4);
   PSR <- UNKNOWN;
   CurrentMode <- Mode_Handler;
   PSR.ExceptionNumber <- ExceptionNumber;
   CONTROL.SPSEL <- false;
   ExceptionActive(ExceptionNumber) <- true
}


unit ExceptionEntry () =
   match pending
   {
     case Some(e) => { PushStack(); ExceptionTaken (ExcNumber (e)) }
     case None => nothing
   }

unit PopStack (frameptr::word, EXC_RETURN::bits(28)) =
{
   R(0)  <- MemA(frameptr, 4);
   R(1)  <- MemA(frameptr + 0x4, 4);
   R(2)  <- MemA(frameptr + 0x8, 4);
   R(3)  <- MemA(frameptr + 0xC, 4);
   R(12) <- MemA(frameptr + 0x10, 4);
   LR    <- MemA(frameptr + 0x14, 4);
   PC    <- MemA(frameptr + 0x18, 4);
   psr`32 = MemA(frameptr + 0x1C, 4);
   -- when HaveFPExt() do ...
   spmask`32 = ZeroExtend (psr<9:9> : '00');
   match EXC_RETURN<3:0>
   {
      case '_ 001' => SP_main <- (SP_main + 0x20) || spmask
      case '1101' => SP_process <- (SP_process + 0x20) || spmask
      case _ => nothing
   };
   &PSR<31:27> <- psr<31:27>;
   &PSR<24> <- psr<24>;
   &PSR<5:0> <- psr<5:0>
}

unit DeActivate (ReturningExceptionNumber::bits(6)) =
   ExceptionActive(ReturningExceptionNumber) <- false

bool IsOnes(w::bits(N)) = w == -1

nat ExceptionActiveBitCount () =
{
   var count = 0n0;
   for i in 0 .. 63 do when ExceptionActive ([i]) do count <- count + 1;
   return count
}

unit ExceptionReturn(EXC_RETURN::bits(28)) =
{
   when CurrentMode != Mode_Handler do #ASSERT ("CurrentMode == Mode_Handler");
   when !IsOnes(EXC_RETURN<27:4>) do #UNPREDICTABLE ("ExceptionReturn");
   ReturningExceptionNumber = PSR.ExceptionNumber;
   NestedActivation = ExceptionActiveBitCount();
   if not ExceptionActive(ReturningExceptionNumber) then
      #UNPREDICTABLE ("ExceptionReturn")
   else
   {
      var frameptr;
      match EXC_RETURN<3:0>
      {
        case '0001' =>
           if NestedActivation == 1 then
              #UNPREDICTABLE ("ExceptionReturn")
           else
           {
              frameptr <- SP_main;
              CurrentMode <- Mode_Handler;
              CONTROL.SPSEL <- false
           }
        case '1001' =>
           if NestedActivation != 1 then
              #UNPREDICTABLE ("ExceptionReturn")
           else
           {
              frameptr <- SP_main;
              CurrentMode <- Mode_Thread;
              CONTROL.SPSEL <- false
           }
        case '1101' =>
           if NestedActivation != 1 then
              #UNPREDICTABLE ("ExceptionReturn")
           else
           {
              frameptr <- SP_process;
              CurrentMode <- Mode_Thread;
              CONTROL.SPSEL <- true
           }
        case _ => #UNPREDICTABLE ("ExceptionReturn")
      };
      DeActivate (ReturningExceptionNumber);
      PopStack (frameptr, EXC_RETURN);
      if CurrentMode == Mode_Handler then
         when PSR.ExceptionNumber == '000000' do
            #UNPREDICTABLE ("ExceptionReturn")
      else
         when PSR.ExceptionNumber != '000000' do
            #UNPREDICTABLE ("ExceptionReturn")
   }
}

unit CallSupervisor() = Raise (SVCall)

unit BranchTo (address::word) = PC <- address

unit BranchWritePC (address::word) =
   BranchTo (address<31:1> : '0')

unit BXWritePC (address::word) =
   if CurrentMode == Mode_Handler and address<31:28> == '1111' then
      ExceptionReturn(address<27:0>)
   else
   {
      when not address<0> do Raise (HardFault);
      BranchTo (address<31:1> : '0')
   }

unit BLXWritePC (address::word) =
{
   when not address<0> do Raise (HardFault);
   BranchTo (address<31:1> : '0')
}

unit LoadWritePC (address::word) = BXWritePC (address)

unit ALUWritePC (address::word) = BranchWritePC (address)

declare pcinc :: word

unit IncPC() = BranchTo (REG (RName_PC) + pcinc)

--------------------------------
-- Bit and arithmetic operations
--------------------------------

int HighestSetBit (w::bits(N)) = if w == 0 then -1 else [Log2 (w)]

nat CountLeadingZeroBits (w::bits(N)) = [[N] - 0i1 - HighestSetBit (w)]

nat LowestSetBit (w::bits(N)) = CountLeadingZeroBits (Reverse (w))

nat BitCount (w::bits(N)) =
{  var result = 0;
   for i in 0 .. N - 1 do
      when w<i> do result <- result + 0n1;
   return result
}

bits(N) SignExtendFrom (w::bits(N), p::nat) =
{  s = N - p;
   return w << s >> s
}

bits(N) Extend (unsigned::bool, w::bits(M)) =
   if unsigned then ZeroExtend (w) else SignExtend (w)

int UInt (w::bits(N)) = [[w]::nat]

-- Shifts --

bits(N) * bool LSL_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "LSL_C";
   extended_x = [x] : (0s0 ^ shift);
   ( x << shift, extended_x<N> )
}

bits(N) LSL (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (LSL_C (x, shift))

bits(N) * bool LSR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "LSR_C";
   ( x >>+ shift, shift <= N and x<shift-1> )
}

bits(N) LSR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (LSR_C (x, shift))

bits(N) * bool ASR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "ASR_C";
   ( x >> shift, x<Min(N, shift)-1> )
}

bits(N) ASR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (ASR_C (x, shift))

bits(N) * bool ROR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "ROR_C";
   result = x #>> shift;
   ( result, Msb (result) )
}

bits(N) ROR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (ROR_C (x, shift))

bits(N) * bool RRX_C (x::bits(N), carry_in::bool) =
{  result = [[carry_in] : ([x]::bool list)<N-1:1>] :: bits(N);
   ( result, x<0> )
}

bits(N) RRX (x::bits(N), carry_in::bool) =
   Fst (RRX_C (x, carry_in))

-- Decode immediate values

construct SRType { SRType_LSL SRType_LSR SRType_ASR SRType_ROR SRType_RRX }

SRType * nat DecodeImmShift (typ::bits(2), imm5::bits(5)) =
   match typ
   { case '00' => SRType_LSL, [imm5]
     case '01' => SRType_LSR, if imm5 == 0b00000 then 32 else [imm5]
     case '10' => SRType_ASR, if imm5 == 0b00000 then 32 else [imm5]
     case '11' => if imm5 == 0b00000 then SRType_RRX, 1 else SRType_ROR, [imm5]
   }

SRType DecodeRegShift (typ::bits(2)) =
   match typ
   { case '00' => SRType_LSL
     case '01' => SRType_LSR
     case '10' => SRType_ASR
     case '11' => SRType_ROR
   }

bits(N) * bool Shift_C
                 (value::bits(N), typ::SRType, amount::nat, carry_in::bool) =
{  -- when typ == SRType_RRX and amount != 1 do #ASSERT("Shift_C");

   if amount == 0 then
      value, carry_in
   else
      match typ
      { case SRType_LSL => LSL_C (value, amount)
        case SRType_LSR => LSR_C (value, amount)
        case SRType_ASR => ASR_C (value, amount)
        case SRType_ROR => ROR_C (value, amount)
        case SRType_RRX => RRX_C (value, carry_in)
      }
}

bits(N) Shift (value::bits(N), typ::SRType, amount::nat, carry_in::bool) =
   Fst (Shift_C (value, typ, amount, carry_in))

-- Data processing operations

bits(N) * bool * bool AddWithCarry (x::bits(N), y::bits(N), carry_in::bool) =
{  unsigned_sum = [x] + [y] + [carry_in] :: nat;
   signed_sum = [x] + [y] + [carry_in] :: int;
   result = [unsigned_sum]::bits(N);
   carry_out = [result] != unsigned_sum;
   overflow = [result] != signed_sum;
   return result, carry_out, overflow
}

word * bool * bool DataProcessingALU (opc::bits(4), a::word, b::word, c::bool) =
   match opc
   { case '0000' or '1000' => a && b, c, UNKNOWN          -- AND, TST
     case '0001' or '1001' => a ?? b, c, UNKNOWN          -- EOR, TEQ
     case '0010' or '1010' => AddWithCarry (a, ~b, true)  -- SUB, CMP
     case '0011'           => AddWithCarry (~a, b, true)  -- RSB
     case '0100' or '1011' => AddWithCarry (a, b, false)  -- ADD, CMN
     case '0101'           => AddWithCarry (a, b, c)      -- ADC
     case '0110'           => AddWithCarry (a, ~b, c)     -- SBC
     case '0111'           => AddWithCarry (~a, b, c)     -- RSC
     case '1100'           => a || b, c, UNKNOWN          -- ORR
     case '1101'           => b, c, UNKNOWN               -- MOV
     case '1110'           => a && ~b, c, UNKNOWN         -- BIC
     case '1111'           => ~b, c, UNKNOWN              -- MVN
   }

bool ArithmeticOpcode (opc::bits(4)) =
   (opc<2> or opc<1>) and not (opc<3> and opc<2>)
