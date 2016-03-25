open String

(* TODO: *)
(* it should be possible to functions and global variables before they are defined *)
(* zijn er nog types uit de AST te slopen? vardecl en fundecl niet. *)
(* onze tokenizer moet comments wegmieteren *)

(* besluiten *)
(* "<type> id = exp" maakt een id *)
(* "var id = exp" verandert een id *) 

type requestresult = Success of info * string | Request of string
(* als een id nog niet gedefinieerd is, terwijl hij wel nodig is, wordt een request voor dat id gegeven *)

type info = (* alle side information nodig naast de structure en de code *)
	{
		idtypes: (string * typetoken) list
	}

(* exp_infix voorbeeld *)
(* 2 + 3 *)
(*LDC	2
	LDC	3
	ADD *)

let rec exp_gen info exp =
	match exp with
	| Exp_field fieldexp -> field_gen fieldexp
	| Exp_infix (exp1,op,exp2) -> 
		match exp_gen info exp1 with
		| Success (info,code1) -> 
			match exp_gen info exp2 with
			| Success (info,code2) ->
				| info, append (code1) (append (code2) (op2_gen op))

let vardecl_gen info code decl = 
	match decl with
	| Vardecl (Some (typetoken),id,exp) ->
		match exp_gen info exp with
		match typetoken with
		| Basictype _ -> 

let spl_gen code info structure = 
  	let spl_gen' code info = function
  	| [] -> code
  	| Decl_var decl -> vardecl_gen code info decl
  	| Decl_fun decl -> fundecl_gen code info decl in
	match structure with
	| SPL decllist -> spl_gen' code info decllist