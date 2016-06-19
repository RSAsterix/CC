open Types
open List

let matchindex = ref 0;;

let fid_to_mid fid = "|"^(string_of_int !matchindex)^fid



let rec get_matchvars_caselist fid = function
	| (_,_,stmt_list)::caselist -> List.append (get_matchvars fid stmt_list) (get_matchvars_caselist fid caselist)
	| [] -> []
and
get_matchvars fid = function
	| (Stmt_match (exp,case_list))::stmt_list -> matchindex := !matchindex + 1;
		let matchvar = (None,fid_to_mid fid,exp) in
		let matchvars = get_matchvars_caselist fid case_list in
		List.append (matchvar::matchvars) (get_matchvars fid stmt_list)
	| (Stmt_if (exp,ifbody))::stmt_list ->
		List.append (get_matchvars fid ifbody) (get_matchvars fid stmt_list)
	| (Stmt_if_else (exp,ifbody,elsebody))::stmt_list ->
		List.append (get_matchvars fid ifbody) (append (get_matchvars fid elsebody) (get_matchvars fid stmt_list))
	| (Stmt_while (exp,whilebody))::stmt_list ->
		List.append (get_matchvars fid whilebody) (get_matchvars fid stmt_list)
	| _::stmt_list -> get_matchvars fid stmt_list
	| [] -> []

type varbeschrijving = op1 option * fieldexp

type stelling_extract = {
	vars: (id * varbeschrijving) list;
	predicates: exp list;
	werkruimte: varbeschrijving;
}

let to_negated_predicate varbeschrijving exp : exp =
	match varbeschrijving with
	| None,fieldexp -> Exp_infix(Exp_field fieldexp,Eqop Neq,exp)
	| Some op1, fieldexp -> Exp_infix(Exp_prefix(op1,Exp_field fieldexp),Eqop Neq,exp)

let to_predicate varbeschrijving exp : exp =
	match varbeschrijving with
	| None,fieldexp -> Exp_infix(Exp_field fieldexp,Eqop Eq,exp)
	| Some op1, fieldexp -> Exp_infix(Exp_prefix(op1,Exp_field fieldexp),Eqop Eq,exp)

let add_to_vars mid extract id : stelling_extract =
	{vars=((id,extract.werkruimte)::extract.vars);predicates=extract.predicates;werkruimte=(None,Nofield mid)}

let add_to_predicates mid extract exp : stelling_extract =
	{vars=extract.vars;predicates=(to_predicate extract.werkruimte exp)::extract.predicates;werkruimte=(None,Nofield mid)}

let merge_extracts mid extract1 extract2 : stelling_extract =
	{vars=(List.append extract2.vars extract1.vars);
	predicates=(List.append extract2.predicates extract1.predicates);
	werkruimte=(None,Nofield mid)
	}

(*deze functie moet uit de stelling twee dingen genereren: *)
(* alle hyperlokale variabelen en hoe je ze bereikt *)
(* alle te vragen predicates *)
(* verder heb je een werkruimte nodig*)
let rec rmc_stelling mid extract = function
	| Exp_field (Nofield id) -> add_to_vars mid extract id
	| Exp_field _ -> raise Not_found
	| Exp_prefix (op1,exp) -> rmc_stelling mid {extract with werkruimte=(Some op1,snd extract.werkruimte)} exp 
	| Exp_int i -> add_to_predicates mid extract (Exp_int i)
	| Exp_char c -> add_to_predicates mid extract (Exp_char c)
	| Exp_bool b -> add_to_predicates mid extract (Exp_bool b)
	| Exp_emptylist -> add_to_predicates mid extract (Exp_emptylist)
	| Exp_constructor c -> add_to_predicates mid extract (Exp_constructor c)
	| Exp_tuple (exp1,exp2) -> merge_extracts mid
		(rmc_stelling mid {vars=[];predicates=[];werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte,Fst))} exp1)
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte, Snd))} exp2)
	| Exp_low_bar -> extract
	| Exp_function_call _ -> raise Not_found
	| Exp_infix (exp1,Listop,exp2) -> merge_extracts mid
		(rmc_stelling mid {vars=[];predicates=[(to_negated_predicate extract.werkruimte Exp_emptylist)];werkruimte=(fst extract.werkruimte,Field (snd extract.werkruimte,Hd))} exp1)
		(rmc_stelling mid {extract with werkruimte=(fst extract.werkruimte, Field (snd extract.werkruimte, Tl))} exp2)
	| Exp_infix _ -> raise Not_found	

let rmc_hyperlocalvar id (vars : (id*varbeschrijving) list) =
	try
		snd (List.find (fun (x : (id*varbeschrijving)) -> fst x = id) vars)
	with
	| Not_found -> (None,Nofield id);;

let rec rmc_fieldexp vars = function
	| Nofield id -> rmc_hyperlocalvar id vars
	| Field (fieldexp,field) -> 
		let (op1option,fieldexp) = rmc_fieldexp vars fieldexp in
		(op1option,Field (fieldexp,field))  

let rec rmc_exp vars = function
	| Exp_field fieldexp ->
		(match rmc_fieldexp vars fieldexp with
		| None, fieldexp -> Exp_field fieldexp
		| Some op1, fieldexp -> Exp_prefix (op1,Exp_field fieldexp))
	| Exp_infix (exp1,op2,exp2) -> Exp_infix (rmc_exp vars exp1, op2, rmc_exp vars exp2)
	| Exp_prefix (op1,exp) -> Exp_prefix (op1, rmc_exp vars exp)
	| Exp_function_call (id,explist) -> Exp_function_call (id,List.map (rmc_exp vars) explist)
	| Exp_tuple (exp1,exp2) -> Exp_tuple (rmc_exp vars exp1, rmc_exp vars exp2)
	| exp -> exp

let rec rmc_caselist vars = function
	| (exp,None,stmtlist)::caselist ->
		(rmc_exp vars exp,None,rmc_antwoord vars stmtlist)::(rmc_caselist vars caselist)
	| (exp,Some exp2,stmtlist)::caselist ->
		(rmc_exp vars exp, Some (rmc_exp vars exp2), rmc_antwoord vars stmtlist)::rmc_caselist vars caselist
	| [] -> []
and
rmc_antwoord vars = function
	| Stmt_if (exp,ifbody)::stmt_list -> 
		Stmt_if (rmc_exp vars exp,rmc_antwoord vars ifbody)::(rmc_antwoord vars stmt_list)
	| Stmt_if_else (exp,ifbody,elsebody)::stmt_list ->
		Stmt_if_else (rmc_exp vars exp, rmc_antwoord vars ifbody, rmc_antwoord vars ifbody)::(rmc_antwoord vars stmt_list)
	| Stmt_while (exp,whilebody)::stmt_list ->
		Stmt_while (rmc_exp vars exp, rmc_antwoord vars whilebody)::(rmc_antwoord vars stmt_list)
	| Stmt_define (fieldexp,exp)::stmt_list -> 
		(match rmc_fieldexp vars fieldexp with
		| None, fieldexp -> Stmt_define (fieldexp, rmc_exp vars exp)::(rmc_antwoord vars stmt_list)
		| Some op1, fieldexp -> Stmt_define (fieldexp, Exp_prefix (op1,rmc_exp vars exp))::(rmc_antwoord vars stmt_list))
	| Stmt_function_call (fid,explist)::stmt_list -> 
		Stmt_function_call (fid,(map (rmc_exp vars) explist))::(rmc_antwoord vars stmt_list)
	| Stmt_return None::stmt_list -> 
		Stmt_return None::(rmc_antwoord vars stmt_list)
	| Stmt_return (Some exp)::stmt_list ->
		Stmt_return (Some (rmc_exp vars exp))::(rmc_antwoord vars stmt_list)
	| Stmt_match (exp,caselist)::stmt_list ->
		Stmt_match (rmc_exp vars exp,rmc_caselist vars caselist)::(rmc_antwoord vars stmt_list)	
	| [] -> []

let rmc_case mid = function
	| stelling, whenpredicate, antwoord ->
		let stelling_extract = rmc_stelling mid {vars=[];predicates=[];werkruimte=(None,Nofield mid)} stelling in
		let whenpredicate =
			(match whenpredicate with
			| None -> Exp_bool true
			| Some whenpredicate -> rmc_exp stelling_extract.vars whenpredicate) in
	let antwoord = rmc_antwoord stelling_extract.vars antwoord in
		((List.fold_left (fun a b -> Exp_infix (a,Logop And, b)) whenpredicate stelling_extract.predicates), antwoord)

(* missing match case: when an match stmt is given with no cases. This possibility is removed earlier*)
let rec to_ifstmts = function
	| [] -> raise Not_found
	| (predicate, ifbody)::[] -> Stmt_if (predicate, ifbody)
	| (predicate,ifbody)::case_list -> Stmt_if_else (predicate,ifbody,[to_ifstmts case_list])

let rec remove_trues_exp = function
	| Exp_infix(Exp_bool true,Logop And,rest) -> 
		remove_trues_exp rest
	| Exp_infix(exp,Logop And,Exp_bool true) ->
		exp
	| Exp_infix(exp,Logop And,rest) ->
		Exp_infix(exp,Logop And,remove_trues_exp rest)
	| exp -> exp

let rec remove_trues_stmt = function
	| Stmt_if (Exp_bool true,stmt_list) -> stmt_list
	| Stmt_if_else (Exp_bool true,stmt_list,[rest]) -> stmt_list
	| Stmt_if (exp,stmt_list) -> [Stmt_if(remove_trues_exp exp,stmt_list)]
	| Stmt_if_else (exp,stmt_list,[rest]) -> [Stmt_if_else(remove_trues_exp exp,stmt_list,remove_trues_stmt rest)]
	| _ -> raise Not_found

let rec rmc_match_stmt fid = function
	| exp, case_list -> 
		let mid = fid_to_mid fid in
		let case_list = List.map (rmc_case mid) case_list in
		let ifstmts = rmc_stmt_list fid (remove_trues_stmt (to_ifstmts case_list)) in
		ifstmts
and
rmc_stmt_list fid (stmt_list: stmt list) = match stmt_list with
	| (Stmt_match (exp, case_list))::stmt_list -> matchindex := !matchindex + 1; append (rmc_match_stmt fid (exp,case_list)) (rmc_stmt_list fid stmt_list)
	| (Stmt_if (exp,ifbody))::stmt_list ->
		Stmt_if (exp,(rmc_stmt_list fid ifbody))::(rmc_stmt_list fid stmt_list)
	| (Stmt_if_else (exp,ifbody,elsebody))::stmt_list ->
		Stmt_if_else (exp,(rmc_stmt_list fid ifbody),(rmc_stmt_list fid elsebody))::(rmc_stmt_list fid stmt_list)
	| (Stmt_while (exp,whilebody))::stmt_list ->
		Stmt_while (exp,(rmc_stmt_list fid whilebody))::(rmc_stmt_list fid stmt_list)
	| head::tail -> head::(rmc_stmt_list fid tail)
	| [] -> []

let rmc_fundecl = function
	| (fid,fargs,funtype,vardecl_list,stmt_list) -> 
		let vardecl_list = matchindex := 0; List.append vardecl_list (get_matchvars fid stmt_list) in
		let stmt_list = matchindex := 0; rmc_stmt_list fid stmt_list in
		Fundecl(fid,fargs,funtype,vardecl_list,stmt_list)
		
let rec rmc_spl = function
	| (Fundecl x)::spl -> (rmc_fundecl x)::(rmc_spl spl)
	| head::tail -> head::(rmc_spl tail)
	| [] -> []