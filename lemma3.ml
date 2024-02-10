#use "lemma1.ml";;

(* Ustalmy n, m *)
let n = fresh_var ();;
let m = fresh_var ();;

let zero = Const "0";;

let goal = Equal (Fun ("+", [Var n; Fun ("S", [Var m])]), Fun ("S", [Fun ("+", [Var n; Var m])]));;

(* Stawiamy tezę indukcyjną: *)
let ind = theorem_of_axiom (InductionScheme (n, goal));;

(*=============================================== OBSERWACJA 1 ===============================*)
let obs1 = a_e (theorem_of_axiom ZeroAddition) (Fun ("S", [Var m]));;
let obs2 = a_e (theorem_of_axiom ZeroAddition) (Var m);;
(*=============================================================================================*)

(* Zauważmy, że: *)
let obs3 = theorem_of_axiom (SubstitutionEquality (n, Equal (Fun ("+", [zero; Fun ("S", [Var m])]), Fun ("S", [Var n]))));;
let obs3 = a_e obs3 (Var m);;
let obs3 = a_e obs3 (Fun ("+", [zero; Var m]));;

(* Przypomnijmy sobie lemat 1 (o symetrii równości) *)
equalitySymmetryLemma;;

(* Zastosujmy go do 0+m i m *)
let step1 = a_e equalitySymmetryLemma (Fun ("+", [zero; Var m]));;
let step2 = a_e step1 (Var m);;

let step3 = imp_e step2 obs2;;
let step4 = imp_e obs3 step3;;
let step5 = imp_e step4 obs1;;

let step6 = imp_e ind step5;;

let assume = by_assumptions goal;;

let k = fresh_var ();;
let obs4 = theorem_of_axiom (SubstitutionEquality (k, Equal (Fun ("S", [Var k]), Fun ("S", [Fun ("S", [Fun ("+", [Var n; Var m])])]))));;
let obs4 = a_e obs4 (Fun ("S", [Fun ("+", [Var n; Var m])]));;
let obs4 = a_e obs4 (Fun ("+", [Var n; Fun ("S", [Var m])]));;

let obs5 = a_e equalitySymmetryLemma (Fun ("+", [Var n; Fun ("S", [Var m])]));;
let obs5 = a_e obs5 (Fun ("S", [Fun ("+", [Var n; Var m])]));;

let obs5 = imp_e obs5 assume;;
let step7 = imp_e obs4 obs5;;

let obs6 = a_e (theorem_of_axiom EqualityReflectivity) (Fun ("S", [Fun ("S", [Fun ("+", [Var n; Var m])])]));;
let step8 = imp_e step7 obs6;;

let obs7 = theorem_of_axiom SuccesorAddition;;
let obs7 = a_e obs7 (Var n);;
let obs7 = a_e obs7 (Fun ("S", [Var m]));;

let obs8 = a_e equalitySymmetryLemma (Fun ("+", [Fun ("S", [Var n]); Fun ("S", [Var m])]));;
let obs8 = a_e obs8 (Fun ("S", [Fun ("+", [Var n; Fun ("S", [Var m])])]));;

let obs9 = theorem_of_axiom (SubstitutionEquality (k, Equal (Var k, (Fun ("S", [Fun ("S", [Fun ("+", [Var n; Var m])])])))));;
let obs9 = a_e obs9 (Fun ("S", [Fun ("+", [Var n; Fun ("S", [Var m])])]));;
let obs9 = a_e obs9 (Fun ("+", [Fun ("S", [Var n]); Fun ("S", [Var m])]));;

let step9 = imp_e obs8 obs7;;
let step10 = imp_e obs9 step9;;
let step11 = imp_e step10 step8;;

let obs10 = theorem_of_axiom (SubstitutionEquality (k, Equal (Fun ("S", [Var k]), Fun ("S", [Fun ("+", [Fun ("S", [Var n]); Var m])]))));;
let obs10 = a_e obs10 (Fun ("+", [Fun ("S", [Var n]); Var m]));;
let obs10 = a_e obs10 (Fun ("S", [Fun ("+", [Var n; Var m])]));;

let helper1 = a_e (a_e (theorem_of_axiom SuccesorAddition) (Var n)) (Var m);;
let helper2 = a_e (theorem_of_axiom EqualityReflectivity) (Fun ("S", [Fun ("+", [Fun ("S", [Var n]); Var m])]));;

let obs10 = imp_e (imp_e obs10 helper1) helper2;;

let helper3 = a_e (a_e equalitySymmetryLemma (Fun ("+", [Fun ("S", [Var n]); Fun ("S", [Var m])]))) 
                  (Fun ("S", [Fun ("S", [Fun ("+", [Var n; Var m])])]));;
let obs11 = imp_e helper3 step11;;
let obs12 = theorem_of_axiom (SubstitutionEquality (k, Equal (Var k, Fun ("S", [Fun ("+", [Fun ("S", [Var n]); Var m])]))));;
let obs12 = a_e obs12 (Fun ("S", [Fun ("S", [Fun ("+", [Var n; Var m])])]));;
let obs12 = a_e obs12 (Fun ("+", [Fun ("S", [Var n]); Fun ("S", [Var m])]));;

let step12 = imp_e obs12 obs11;;
let step13 = imp_e step12 obs10;;

let step14 = imp_i (consequences assume) step13;;

let step15 = a_i step14 n;;
let step16 = imp_e step6 step15;;

let reverseSuccessorAdditionLemma = step16;;
