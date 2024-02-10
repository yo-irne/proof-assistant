type variable = string
type constant = string
type symbol = string

module Subst = Map.Make(String)

type term = 
  | Var of variable
  | Const of constant
  | Fun of symbol * (term list)

(* let infix = ["+"; "*"] *)

type formula =
  | Bot
  | Equal of term * term
  | Pred of symbol * (term list)
  | Imp of formula * formula
  | Forall of variable * formula

let rec string_of_term t = 
  match t with
    | Var v -> v
    | Const c -> c
    | Fun (f, []) -> f
    | Fun ("+", [t1; t2]) -> (string_of_term t1) ^ " + " ^ (string_of_term t2)
    | Fun ("*", [t1; t2]) -> (string_of_term t1) ^ " * " ^ (string_of_term t2)
    | Fun (f, a::args) -> 
        let printed_args =
          (string_of_term a) ^ List.fold_left (fun x y -> x ^ ", " ^ y) "" (List.map string_of_term args)
        in f ^ "(" ^ printed_args ^ ")"

let rec string_of_formula f = 
  match f with
    | Bot -> "⊥"
    | Equal (t1, t2) -> (string_of_term t1) ^ " = " ^ (string_of_term t2)
    | Pred (p, []) -> p
    | Pred (p, a::args) -> 
        let printed_args = 
          (string_of_term a) ^ List.fold_left (fun x y -> x ^ ", " ^ y) "" (List.map string_of_term args)
        in p ^ "(" ^ printed_args ^ ")"
    | Imp (f1, f2) -> (string_of_formula f1) ^ " → " ^ (string_of_formula f2)
    | Forall (x, f') -> 
        match f' with
          | Forall (x', f'') -> "(∀ " ^ x ^ ")" ^ (string_of_formula f')
          | _ -> "(∀ " ^ x ^ ")(" ^ (string_of_formula f') ^ ")"

(* ======================== Helpers ======================== *)

let counter = 
  let clock = ref 0 in fun () ->
    clock := !clock + 1;
    !clock

let fresh_var = fun () ->
  "x" ^ (string_of_int (counter ()))

let rec mem a xs =
  match xs with 
    | [] -> false
    | x::xs -> if x = a then true else mem a xs 

let rec forall xs p =
  match xs with
    | [] -> true
    | x::xs -> (p x) && (forall xs p)

let union xs ys =
  List.fold_left (fun hs x -> if forall hs (fun a -> a <> x) then x::hs else hs) xs ys

(* ======================== Substitutions ======================== *)

let rec is_free_in_term v t =
  match t with
    | Var v' -> not (v = v')
    | Const c -> true
    | Fun (f, args) -> forall args (is_free_in_term v)

let is_free_in_terms v ts = forall ts (is_free_in_term v)

let rec is_free_in_formula v f =
  match f with
    | Bot -> true
    | Equal (t1, t2) -> is_free_in_terms v [t1;t2]
    | Pred (p, args) -> is_free_in_terms v args
    | Imp (f1, f2) -> (is_free_in_formula v f1) && (is_free_in_formula v f2)
    | Forall (v', f') -> (not (v = v')) && (is_free_in_formula v f')

let rec psubst_in_term subst t =
  if Subst.is_empty subst then t else
    match t with
      | Var v -> 
        begin match Subst.find_opt v subst with
          | None -> Var v
          | Some t -> t
        end
      | Const c -> Const c
      | Fun (f, args) -> Fun (f, List.map (psubst_in_term subst) args)

let rec is_free_in_subst v subst =
  match subst with
    | [] -> true
    | x::xs -> (is_free_in_term v (snd x)) && (is_free_in_subst v xs)

let rec psubst_in_formula subst f =
  if Subst.is_empty subst then f else
    match f with
      | Bot -> Bot
      | Equal (t1, t2) -> Equal (psubst_in_term subst t1, psubst_in_term subst t2)
      | Pred (p, args) -> Pred (p, (List.map (psubst_in_term subst) args))
      | Imp (f1, f2) -> Imp (psubst_in_formula subst f1, psubst_in_formula subst f2)
      | Forall (v, f') -> if Subst.mem v subst 
          then psubst_in_formula (Subst.remove v subst) f'
          else if is_free_in_subst v (Subst.bindings subst)
            then Forall (v, psubst_in_formula subst f')
            else let v' = fresh_var () in 
              Forall (v', psubst_in_formula (Subst.add v (Var v') subst) f')

let subst_in_term x sub = psubst_in_term (Subst.singleton x sub)
let subst_in_formula x sub = psubst_in_formula (Subst.singleton x sub)

(* ======================== Other operations on formuli ======================== *)

(* let rec unify f g = *) (* TODO *)

let rec equiv f g =
  match f, g with 
    | Forall (v1, f'), Forall (v2, g') -> 
      let v = fresh_var () in 
        equiv (subst_in_formula v1 (Var v) f') (subst_in_formula v2 (Var v) g')
    | Imp (f1, f2), Imp (g1, g2) -> (equiv f1 g1) && (equiv f2 g2)
    | _, _ -> f = g
    (* | _, _ -> (unify f g) = g *)

(* ======================== Printers ======================== *)

let pp_print_formula fmtr f =
  Format.pp_print_string fmtr (string_of_formula f)

let pp_print_term fmtr t =
  Format.pp_print_string fmtr (string_of_term t)

let pp_print_var fmtr v =
  Format.pp_print_string fmtr v







