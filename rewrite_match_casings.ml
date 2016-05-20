let fid_to_mid i fid = "|"^(int_to_string i)^fid

let get_matchvars fid i = function
	| (Stmt_match exp, case_list)::stmt_list -> (None,fid_to_mid i id,exp)::(get_matchvars fid (i+1) stmt_list)
	| _ -> get_matchvars fid i stmt_list

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
	{vars=(append extract2.vars extract1.vars);
	predicates=(append extract2.predicates extract1.predicates);
	werkruimte=(None,Nofield mid)
	}

(*deze functie moet uit de stelling twee dingen genereren: *)
(* alle hyperlokale variabelen en hoe je ze bereikt *)
(* alle te vragen predicates *)
(* verder heb je een werkruimte nodig*)
let rmc_stelling mid extract = function
	| Exp_field (Nofield id) -> add_to_vars mid extract id
	| Exp_prefix (op1,exp) -> rmc_stelling mid {extract with werkruimte=(Some op1,snd extract.werkruimte)} exp 
	| Exp_int i -> add_to_predicates mid extract (Exp_int i)
	| Exp_char c -> add_to_predicates mid extract (Exp_char c)
	| Exp_bool b -> add_to_predicates mid extract (Exp_bool b)
	| Exp_emptylist -> add_to_predicates mid extract (Exp_emptylist)
	| Exp_constructor c -> add_to_predicates mid extract (Exp_constructor c)
	| Exp_tuple (exp1,exp2) -> merge_extracts 
		(rmc_stelling mid {vars=[];predicates=[];werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte,Fst))} exp1)
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte, Snd))} exp2)
	| Exp_low_bar -> extract
	| Exp_infix (exp1,Listop,exp2) -> merge_extracts
		(rmc_stelling mid {vars=[];predicates=[];werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte,Hd))} exp1)
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte, Field (snd extract.werkruimte, Tl))} exp2)

let rmc_hyperlocalvar id (vars : (id*varbeschrijving) list) =
	try
		snd (List.find (fun (x : (id*varbeschrijving)) -> fst x = id))
	with
	| Not_found -> (None,Nofield id);;

let rec rmc_whenpredicate_fieldexp vars = function
	| Nofield id -> rmc_hyperlocalvar id vars
	| Field fieldexp,field -> 
		let (op1option,fieldexp) = rmc_whenpredicate_fieldexp vars fieldexp in
		(op1option,Field (fieldexp,field))  

let rmc_whenpredicate vars = function
	| Exp_field fieldexp ->
		(match rmc_whenpredicate_fieldexp vars fieldexp with
		| None, fieldexp -> Exp_field fieldexp
		| Some op1, fieldexp -> Exp_prefix (op1,Exp_field fieldexp))
	| Exp_infix (exp1,op2,exp2) -> Exp_infix (rmc_whenpredicate vars exp1, op2, rmc_whenpredicate vars exp2)
	| Exp_prefix (op1,exp) -> Exp_prefix (op1, rmc_whenpredicate vars exp)
	| Exp_functioncall (id,explist) -> Exp_functioncall (id,List.map (rmc_whenpredicate vars) explist)
	| Exp_tuple (exp1,exp2) -> Exp_tuple (rmc_whenpredicate vars exp1, rmc_whenpredicate vars exp2)
	| exp -> exp

let rmc_case mid = function
	| stelling, whenpredicate, stmt_list ->
		let stelling_extract = rmc_stelling mid {vars=[];predicates=[];werkruimte=(None,Nofield mid)} stelling in
		let whenpredicate =
			(match whenpredicate with
			| None -> Exp_bool true
			| Some whenpredicate -> rmc_whenpredicate stelling_extract.vars whenpredicate) in
		((List.fold_left (&&) whenpredicate stelling_extract.predicates), stmt_list)

let to_ifstmts = function
	| predicate, ifbody::[] -> Stmt_if (predicate, ifbody)
	| predicate,ifbody::case_list -> Stmt_if_else (predicate,ifbody,to_ifstmts case_list)

let rmc_match_stmt fid i = function
	| exp, case_list -> 
		let mid = fid_to_mid i fid in
		let case_list = map (rmc_case mid) case_list in
		let ifstmts = to_ifstmts case_list in
		(Stmt_define ((Nofield mid),exp),if_stmts)

let rmc_stmt_list fid i = function
	| 

let rmc_fundecl = function
	| (fid,fargs,funtype,vardecl_list,stmt_list) -> 
		let vardecl_list = List.append vardecl_list (get_matchvars fid 0 stmt_list) in
		let stmt_list = rmc_stmt_list fid 0 stmt_list
		
let rmc_spl = function
	| (Fundecl x)::spl -> (rmc_fundecl x)::(rmc_spl spl)
	| head::tail -> head::(rmc_spl tail)
	| [] -> []