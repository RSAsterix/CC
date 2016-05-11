(* plan: *)
(* run through the program. *)
(* whenever a variable is declared, remember its startline*)
(* whenever a variable is used, remember its endline*)
(* whenever a variable is declared again, push the original startline and endline and start a new startline*)
(* then make a graph where you check for every variable if they exist at the same time*)

open Types
open Set

module SS = Set.Make(String);;

type varwithlines = {
	id : string;
	lines: int*int list
	}
	
module Vwlforsets =
  struct
   type t = varwithlines
   let compare x y =
    Pervasives.compare x.id y.id
  end

module Vwls = Set.Make(Vwlforsets)

let line = ref 0;;


let var_in_fieldexp = function
	| Nofield id -> id
	| Field (fieldexp,_) -> var_in_fieldexp fieldexp
				
let vars_in_exp = function
	| Exp_field fieldexp -> var_in_fieldexp fieldexp
	| Exp_infix exp1,_,exp2
	| Exp_tuple exp1,exp2 -> SS.union (vars_in_exp exp1) (vars_in_exp exp2)
	| Exp_int
	| Exp_char
	| Exp_bool
	| Exp_emptylist -> SS.empty
	| Exp_function_call (_,explist) -> fold_left union SS.empty (map vars_in_exp explist);;

let get_lines_spl allvarwls = function
	| Vardecl (_,id,exp) -> line := !line + 1; (* id wordt gedefinieerd *)
		let usedvars = vars_in_exp exp in
		if mem id usedvars then (* id is nodig voor zijn eigen definitie *)
			if mem {id=id;lines=[]} allvarwls then
				let varwl = (Vwls.find (fun x -> x.id ) allvars) in
				if varwl.lines = [] then
					(* kan niet aangezien id al eerder gedefinieerd moet zijn *)
				else (* id is al eerder gedefinieerd *)
					Vwls.add {id=id;lines=((fst (hd varwl.lines)),line)::(tl varwl.lines)} (Vwls.remove {id=id;lines=[]} allvarwls)
					(* id is minstens life tot nu *)
