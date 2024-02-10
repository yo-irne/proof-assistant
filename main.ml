#use "fol.ml"
#use "proof.ml"
#use "peano.ml"

module M = Logic(PA)

open M

#install_printer pp_print_var
#install_printer pp_print_term
#install_printer pp_print_formula
#install_printer pp_print_theorem