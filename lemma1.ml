let x = fresh_var ();;
let y = fresh_var ();;

let assume = Equal (Var x, Var y);;
let goal = Equal (Var y, Var x);;

(* ================================================ *)

let step1 = theorem_of_axiom (SubstitutionEquality (y, goal));;

let step2 = a_e step1 (Var x);;
let step3 = a_e step2 (Var y);;

(* ================================================ *)

let step4 = imp_e step3 (by_assumptions assume);;

let obs = a_e (theorem_of_axiom EqualityReflectivity) (Var x);;

(* ================================================ *)

let step5 = imp_e step4 obs;;
let step6 = imp_i assume step5;;

(* ================================================ *)

let step7 = a_i step6 y;;
let step8 = a_i step7 x;;

let equalitySymmetryLemma = step8;;
