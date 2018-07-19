structure otp_utilLib :> otp_utilLib =

struct  
open HolKernel Parse boolLib bossLib
open pairTheory;
open ListPair;
open wordsTheory;

(*
Run these if you are using interactive mode.

loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/l3-machine-code/m0/decompiler")::(!loadPath));
loadPath := ((HOLDIR ^ "/examples/machine-code/hoare-triple")::(!loadPath));
*)

open progTheory;
open m0_decompLib;
open helperLib;

fun dest_all_exists_helper (t :term) exvars exbodies =
    if not (is_exists t) then (exvars, exbodies) else
    let 
       val (exvar, exbody) = dest_exists t;
       val (exvars1, exbodies1) = dest_all_exists_helper exbody exvars exbodies in
       (exvar::exvars1, exbody::exbodies1)
    end;


fun dest_all_exists t =
    dest_all_exists_helper t [] [];


fun subst_bodies _ [] _ = []
  | subst_bodies xvar (xb::xbodies) i = (subst [xvar |-> i] xb)::(subst_bodies xvar xbodies i);

fun subst_all [] [] [] = [] 
  | subst_all (xvar::xvars) (xbody::xbodies) (i::is) = 
      let val (nBody::nBodies) = subst_bodies xvar (xbody::xbodies) i in
      (nBody::(subst_all xvars nBodies is))
 end;


fun POSTC_EXISTS_ELIM def post =
    let 
	val word_rwrs = [WORD_w2w_OVER_BITWISE, WORD_OR_ASSOC, WORD_AND_ASSOC];
        val exthm = SPEC_ALL post; 
	val thm_unwinded = REWRITE_RULE [def, LET_DEF] exthm;
	val thm_simpli = SIMP_RULE (bool_ss ++ w2w_ss) word_rwrs thm_unwinded;
	val tm_specced = dest_all_exists (concl thm_simpli);
	val tm_unspecced = dest_all_exists (concl exthm);
	val tm_ex_vars = fst tm_specced;
	val tm_concl = List.last (snd tm_specced);
	val (tm_lhs, tm_rhs) = dest_eq tm_concl;
	val (list_lhs, list_rhs) = (strip_pair tm_lhs, strip_pair tm_rhs);
	val lhs_rhs = zipEq (list_lhs, list_rhs);
	val filtered_lists = List.filter (fn x => (List.exists(fn y => term_eq (snd x) y) tm_ex_vars)) lhs_rhs;
	val tm_instantiations = List.map (fn x => fst x) filtered_lists;
	val tm_substs = subst_all tm_ex_vars (snd tm_unspecced) tm_instantiations;
	val tm_target = List.last tm_substs;
	val tm_help = mk_imp(concl post, tm_target);
	val thm_target = prove(tm_target,
	   ASSUME_TAC post >> 
           FULL_SIMP_TAC (arith_ss++w2w_ss) (List.concat[[def, LET_DEF], word_rwrs]));
    in (GEN_ALL thm_target)
    end;

fun COMB_PREC_POSTC prec postc =
   let 
      val body =  CONJ (UNDISCH (SPEC_ALL prec)) (SPEC_ALL postc) in 
   (GEN_ALL (DISCH_ALL body))
   end

end
