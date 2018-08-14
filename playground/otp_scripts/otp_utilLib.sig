signature otp_utilLib =
sig
  val get_spec: string -> Thm.thm list -> Thm.thm
  val POSTC_EXISTS_ELIM: Thm.thm -> Thm.thm -> Thm.thm 
  val COMB_PREC_POSTC: Thm.thm -> Thm.thm -> Thm.thm 
end
