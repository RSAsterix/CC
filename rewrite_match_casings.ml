let get_matchvars id i = function
	| (Stmt_match exp, case_list)::stmt_list -> (None,"|"^(int_to_string i)^id,exp)::(get_matchvars id (i+1) stmt_list)
	| _ -> get_matchvars id i stmt_list

type varbeschrijving = op1 option * fieldexp

type stelling_extract = {
	vars: (id * varbeschrijving) list;
	predicates: exp list;
	werkruimte: varbeschrijving;
}

let to_predicate varbeschrijving exp =
	match varbeschrijving with
	| None,fieldexp -> Exp_infix(Exp_field fieldexp,Eqop Eq,exp)
	| Some op1, fieldexp -> Exp_infix(Exp_prefix(op1,Exp_field fieldexp),Eqop Eq,exp)

let add_to_vars mid extract id =
	{vars=((id,extract.werkruimte)::extract.vars);predicates=extract.predicates;werkruimte=(None,Nofield mid)}

let add_to_predicates mid extract exp =
	{vars=extract.vars;predicates=to_predicate extract.werkruimte (Exp_int i);werkruimte=(None,Nofield mid)}

let merge_extracts extract1 extract2 =
	{}

(*deze functie moet uit de stelling twee dingen genereren: *)
(* alle hyperlokale variabelen en hoe je ze bereikt *)
(* alle te vragen predicates *)
(* verder heb je een werkruimte nodig*)
let rmc_stelling mid extract = function
	| Exp_field (Nofield id) -> add_to_vars mid extract id
	| Exp_prefix (op1,exp) -> rmc_stelling 
	| Exp_int i -> add_to_predicates mid extract (Exp_int i)
	| Exp_char c -> add_to_predicates mid extract (Exp_char c)
	| Exp_bool b -> add_to_predicates mid extract (Exp_bool b)
	| Exp_emptylist -> add_to_predicates mid extract (Exp_emptylist)
	| Exp_constructor c -> add_to_predicates mid extract (Exp_constructor c)
	| Exp_tuple (exp1,exp2) -> merge_extracts 
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte,Fst))} exp1)
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte Snd))} exp2)

let rmc_case id = function
	| stelling, predicaat, stmt_list

let rmc_match_stmt = function
	| exp, case_list -> 

let rmc_fundecl = function
	| (id,fargs,funtype,vardecl_list,stmt_list) -> 
		let vardecl_list = List.append vardecl_list (get_matchvars id 0 stmt_list) in
		let stmt_list = rmc_stmt_list
		
let rmc_spl = function
	| (Fundecl x)::spl -> (rmc_fundecl x)::(rmc_spl spl)
	| head::tail -> head::(rmc_spl tail)
	| [] -> []