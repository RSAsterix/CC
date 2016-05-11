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
	func : string;
	lines: int*int list
	}
	
let empty_varwl id func = {id=id;func=func;lines=[]}
	
module Vwlforsets =
  struct
   type t = varwithlines
   let compare x y =
    match Pervasives.compare x.id y.id with
		 | 0 -> Pervasives.compare x.func y.func
     | c -> c
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

let live_till_now allvarwls varwl id func =
	Vwls.add {id=id;func=func;lines=((fst (hd varwl.lines)),line)::(tl varwl.lines)} (Vwls.remove (empty_varwl id func) allvarwls)

let newdefs allvarwls varwl id func =
	Vwls.add (empty_varwl id func) allvarwls

let add_used allvarwls func = function (* zorgt dat de gegeven ids gebruikt worden *)
	|id::usedvars -> 
		let varwl = (Vwls.find (empty_varwl id func) allvars) in
		(live_till_now allvarwls varwl id func)::(add_used allvarwls func usedvars)
		
let add_newdef allvarwls func = function (* voor een lijst van compleet nieuwe ids *)
	| id::newdefs ->
		let varwl = (Vwls.find (empty_varwl id func) allvars) in
		(newly_defined allvarwls id func)::(add_newdef allvarwls func newdefs)

let get_lines_stmts allvarwls func = function
	| Stmt_if

let get_lines_spl allvarwls func = function
	| Vardecl (_,id,exp)::spl -> line := !line + 1; (* id wordt gedefinieerd *)
		let usedvars = vars_in_exp exp in
		let allvarwls = 
  		if mem id usedvars then (* id is nodig voor zijn eigen definitie *)
  			let varwl = (Vwls.find (empty_varwl id func) allvars) in
  			live_till_now allvarwls varwl id func
  			(* de id leeft tot nu *)
  		else (* id wordt nu life. het kan dat hij al eerder bestond en doodging *)
  			if mem (empty_varwl id) allvarwls then (*deze id heeft al eerder geleefd *)
  				let varwl = (Vwls.find (empty_varwl id func) allvars) in
  				if snd (hd varwl.lines) = (-1) then (* de id is gemaakt, maar niet gebruikt *)
  					Vwls.add {id=id;func=func;lines=(line,(-1))::(tl varwl.lines)} (Vwls.remove (empty_varwl id func) allvarwls)
  					(* de laatste keer dat de id is gedefinieerd was niet nuttig en kan worden weggegooid. de id leeft vanaf nu*)
  				else (* de id al eerder gemaakt en gebruikt *)
  					Vwls.add {id=id;func=func;lines=(line,(-1))::(varwl.lines)} (Vwls.remove (empty_varwl id func) allvarwls)
  					(* de laatste keer dat de id heeft geleefd is klaar. We starten een nieuwe levenscyclus *)
  			else (* deze id heeft nog niet eerder geleefd *)
  				Vwls.add {id=id;func=func;lines=[(line,(-1))]} in 
   	get_lines_spl (add_used allvarwls usedvars) func spl
	| Fundecl (func,fargs,_,vardecls,stmts) -> line := !line + 1;
		let allvarwls = add_newdef allvarwls func fargs in
		let allvarwls = add_newdef allvarwls func (map (fun x -> match x with Vardecl _,id,_ -> id) vardecls) in
		get_lines_stmts allvarwls func smts
	| [] -> allvarwls;;


		
			
		
