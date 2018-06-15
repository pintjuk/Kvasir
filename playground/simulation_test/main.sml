open HolKernel boolLib bossLib Parse;
open wordsTheory;
open boolLib;
open pairLib;
open pred_setTheory;
open arithmeticTheory;

(*
Run these if you are using interactive mode.

loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0/decompiler")::(!loadPath));
loadPath := ((HOLDIR ^ "/tools/mlyacc/mlyacclib")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/instruction-set-models/common")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/instruction-set-models/arm")::(!loadPath));

*)

open m0_decompLib;


val (m0_validate_seqh_th, m0_validate_seqh_defs) = m0_decompile "m0_validate_seqh" `
 7803    (*	ldrb	r3, [r0, #0] *)
 7840    (*	ldrb	r0, [r0, #1] *)
 4018    (*	ands	r0, r3 		*)
 09c0    (*	lsrs	r0, r0, #7 *)
`;
