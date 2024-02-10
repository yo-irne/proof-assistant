module type Theory = sig
  open Formula
  
  type axiom
  val theorem_of_axiom : axiom -> formula
end

module Logic(T : Theory) : sig
  open Formula
  
  type theorem
  val premises : theorem -> formula list
  val consequences : theorem -> formula

  val pp_print_theorem : Format.formatter -> theorem -> unit

  val theorem_of_axiom : T.axiom -> theorem
  val by_assumption : formula -> theorem

  val bot_e : formula -> theorem -> theorem

  val imp_i : formula -> theorem -> theorem
  val imp_e : theorem -> theorem -> theorem

  val a_i : theorem -> var -> theorem
  val a_e : theorem -> term -> theorem

end