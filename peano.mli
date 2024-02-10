module type A = sig
    type axiom
    val formula_of_axiom : axiom -> formula
end
  
module PA : A = struct 
  type axiom
  val formula_of_axiom : axiom -> formula
end

