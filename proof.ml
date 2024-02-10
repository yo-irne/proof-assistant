module type Theory = sig
  type axiom
  val something_of_axiom : axiom -> formula
end

module Logic (T : Theory) : sig
  type theorem
  val theorem_of_axiom : T.axiom -> theorem

  val pp_print_theorem : Format.formatter -> theorem -> unit

  val premises : theorem -> (formula list)
  val consequences : theorem -> formula

  (* proving rules *)
  val by_assumptions : formula -> theorem
  val bot_e : formula -> theorem -> theorem
  val imp_i : formula -> theorem -> theorem
  val imp_e : theorem -> theorem -> theorem
  val a_i : theorem -> variable -> theorem
  val a_e : theorem -> term -> theorem

  val theorem_of : (formula list) * formula -> theorem

end = struct

  type theorem = (formula list) * formula
  let premises = fst
  let consequences = snd

  let pp_print_theorem fmtr thm =
    let open Format in
    pp_open_hvbox fmtr 2;
    begin match premises thm with
    | [] -> ()
    | f :: fs ->
      pp_print_formula fmtr f;
      fs |> List.iter (fun f ->
        pp_print_string fmtr ",";
        pp_print_space fmtr ();
        pp_print_formula fmtr f);
      pp_print_space fmtr ()
    end;
    pp_open_hbox fmtr ();
    pp_print_string fmtr "⊢";
    pp_print_space fmtr ();
    pp_print_formula fmtr (consequences thm);
    pp_close_box fmtr ();
    pp_close_box fmtr ()


  let theorem_of_axiom a = ([], T.something_of_axiom a)
  let theorem_of ffs = (fst ffs, snd ffs)

  let by_assumptions f = ([f], f)

  let bot_e f (prem, cons) =
    match cons with
      | Bot -> (prem, f)
      | _ -> failwith "cannot use this rule, consequence of this theorem is not bottom"

  (* let imp_i f (prem, cons) = 
    if mem f prem (* nie zadziałą gdy f \notin prem *)
      then (prem, Imp (f, cons)) 
      else failwith "f not in premises of this theorem"
  *)

  let imp_i f (prem, cons) =
    if mem f prem 
      then ((List.filter (fun g -> f <> g) prem), Imp(f, cons))
      else failwith "cannot magically create theorems"
      
  let imp_e (prem1, cons1) (prem2, cons2) = 
    match cons1 with
      | Imp (f, g) -> if equiv f cons2
          then union prem1 prem2, g
          else failwith "implications do not match"
      | _ -> failwith "cannot use this rule"

  let a_i (prem, cons) v =
    let rec binding_checker prem' v' =
      match prem' with
        | [] -> true
        | p::ps -> (is_free_in_formula v' p) && (binding_checker ps v')
    in if binding_checker prem v
      then (prem, Forall (v, cons))
      else failwith "variable already bound" 

  let a_e (prem, cons) t =
    match cons with
      | Forall (v, f) -> (prem, subst_in_formula v t f)
      | _ -> failwith "incompatible formula structure"

end



