(*
Zgodnie z definicją arytmetyki Peana: 
  L_PA = {+, *, 0, S}
  aksjomaty takie jak niżej PA1 - PA7 (przy czym PA3 to schemat aksjomatu, a nie aksjomat oczywiście) 
  do tego tezy KRL, które być może powinny być bardziej w module proof, ale tu im wygodniej (mi tak naprawdę, nie im)  
*)

module type A = sig
  type axiom =
    | EqualityReflectivity                            (* teza KRL *)
    | SubstitutionEquality of variable * formula      (* teza KRL *)
    | ZeroIsMinimal                                   (* PA 1 *) (* (∀x)(0=Sx → ⊥) *)
    | SuccesorEquality                                (* PA 2 *) (* (∀x)(∀y)(Sx=Sy → x=y) *)
    | InductionScheme of variable * formula           (* PA 3 *) (*  *)
    | ZeroAddition                                    (* PA 4 *) (* (∀x)(0+x=x) *)
    | SuccesorAddition                                (* PA 5 *) (* (∀x)(∀y)(Sx+y = S(x+y)) *)
    | ZeroMultiplication                              (* PA 6 *) (* (∀x)(0*x=0) *)
    | SuccesorMultiplication                          (* PA 7 *) (* (∀x)(∀y)(Sx*y = x*y+y) *)

  val something_of_axiom : axiom -> formula

  (* let succ x = Fun ("S", [x]) *)
end

module PA : A = struct 
  type axiom =
    | EqualityReflectivity 
    | SubstitutionEquality of variable * formula
    | ZeroIsMinimal
    | SuccesorEquality
    | InductionScheme of variable * formula
    | ZeroAddition
    | SuccesorAddition
    | ZeroMultiplication
    | SuccesorMultiplication
  
  let something_of_axiom a =
    match a with
      | EqualityReflectivity ->
          let x = fresh_var () in 
            Forall (x, Equal (Var x, Var x))
      | SubstitutionEquality (v, f) -> 
          let x = fresh_var () in
          let y = fresh_var () in
            Forall (x, Forall (y, Imp ( Equal (Var x, Var y), Imp (
              subst_in_formula v (Var x) f,
              subst_in_formula v (Var y) f))))
      | ZeroIsMinimal ->
          let x = fresh_var () in
            Forall (x, Imp (Equal (Const "0", Fun ("S", [Var x])), Bot))
      | SuccesorEquality ->
          let x = fresh_var () in 
          let y = fresh_var () in
            Forall (x, Forall (y, Imp (
              Equal (Fun ("S", [Var x]), Fun ("S", [Var y])),
              Equal (Var x, Var y))))
      | ZeroAddition -> 
          let x = fresh_var () in
            Forall (x, Equal (Fun ("+", [Const "0"; Var x]), Var x))
      | SuccesorAddition -> 
          let x = fresh_var () in
          let y = fresh_var () in
            Forall (x, Forall (y, Equal (
              Fun ("+", [Fun ("S", [Var x]); Var y]),
              Fun ("S", [Fun ("+", [Var x; Var y])]))))
      | ZeroMultiplication ->
          let x = fresh_var () in
            Forall (x, Equal (Fun ("*", [Const "0"; Var x]), Const "0"))
      | SuccesorMultiplication ->
          let x = fresh_var () in 
          let y = fresh_var () in
            Forall (x, Forall (y, Equal (
              Fun ("*", [Fun ("S", [Var x]); Var y]),
              Fun ("+", [Fun ("*", [Var x; Var y]); Var y]))))
      | InductionScheme (v, f) -> 
          let x = fresh_var () in
            Imp ( subst_in_formula v (Const "0") f, Imp ( 
              Forall (x, Imp (
                subst_in_formula v (Var x) f,
                subst_in_formula v (Fun ("S", [Var x])) f)),
              Forall (x, subst_in_formula v (Var x) f)))
end

