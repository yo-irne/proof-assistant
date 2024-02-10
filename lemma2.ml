let zero = Const "0";;
let n = fresh_var ();;

(* Cel: *)
let goal = Equal (Fun ("+", [Var n; zero]), Var n);;

(* Stawiamy tezę indukcyjną: *)
let ind = theorem_of_axiom (InductionScheme (n, goal));;

(* Zauważmy, że krok zerowy już mamy: *)
let ind0 = a_e (theorem_of_axiom ZeroAddition) zero;;

let step1 = imp_e ind ind0;;

(* Krok indukcyjny: *)
let assume = by_assumptions (Equal (Fun ("+", [Var n; zero]), Var n));;

(* ========================================= OBSERWACJA 1 ====================================*)
(* Zauważmy też, że: *)
let obs1 = theorem_of_axiom SuccesorAddition;;

let obs1 = a_e obs1 (Var n);;
let obs1 = a_e obs1 zero;;

(* A-reguła: *)
let obs1 = a_i obs1 n;;

(* =============================================================================================*)

let m = fresh_var ();;

(* ========================================== OBSERWACJA 2 ===================================== *)
let obs2 = theorem_of_axiom (SubstitutionEquality(n, Equal (
            Fun ("+", [Fun ("S", [Var m]); zero]), 
            Fun ("S", [Var n]))));;

let obs2 = a_e obs2 (Fun ("+", [Var n; zero]));;
let obs2 = a_e obs2 (Var n);;

(* ============================================================================================= *)

(* Korzystamy z obserwacji 2 do naszego założenia: *)
let step2 = imp_e obs2 assume;;
let step3 = a_i step2 m;;

(* Z obserwacji 1 dla n: *)
let step4 = a_e step3 (Var n);;
let step5 = a_e obs1 (Var n);;

(* Z modus ponens: *)
let step6 = imp_e step4 step5;;

(* Korzystamy z założenia indukcyjnego: *)
let step7 = imp_i (consequences assume) step6;;
let step8 = a_i step7 n;;

(* Zatem pokazaliśmy tezę indukcyjną: *)
let step9 = imp_e step1 step8;;

let rightZeroAdditionLemma = step9;;