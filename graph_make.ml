open Graph_lib
open Types
open Printf

module SS = Set.Make(String);;
let print_set s = SS.iter print_endline s;;

let rec fv_exp (free : SS.t) (bound : SS.t) = function
	| Exp_field (Nofield id) when not (SS.mem id bound) -> SS.add id free
	| Exp_field (Field (x,_)) -> fv_exp free bound (Exp_field x)
	| Exp_prefix (_,exp) -> fv_exp free bound exp
	| Exp_infix (exp1,_,exp2) -> SS.union (fv_exp free bound exp1) (fv_exp free bound exp2)
	| Exp_function_call (id, explist) -> fv_exp_list (SS.add id free) bound explist
	| Exp_tuple (exp1,exp2) -> SS.union (fv_exp free bound exp1) (fv_exp free bound exp2)
	| _ -> free
and fv_exp_list (free : SS.t) (bound : SS.t) explist = List.fold_left (fun beginfree exp -> fv_exp beginfree bound exp) free explist;;

let rec fv_stmt (free : SS.t) (bound : SS.t) = function
	| Stmt_if (exp, stmtlist) -> 
		fv_stmt_list (fv_exp free bound exp) bound stmtlist
	| Stmt_if_else (exp, stmtlist1, stmtlist2) ->
		fv_stmt_list (fv_stmt_list (fv_exp free bound exp) bound stmtlist1) bound stmtlist2
	| Stmt_while (exp, stmtlist) ->
		fv_stmt_list (fv_exp free bound exp) bound stmtlist
	| Stmt_define (fieldexp, exp) ->
		fv_exp (fv_exp free bound (Exp_field fieldexp)) bound exp
	| Stmt_function_call (id, explist) -> fv_exp free bound (Exp_function_call (id, explist))
	| Stmt_return (Some exp) -> fv_exp free bound exp
	| _ -> free
and fv_stmt_list (free : SS.t) (bound : SS.t) stmtlist = List.fold_left (fun beginfree stmt -> fv_stmt beginfree bound stmt) free stmtlist;;

let fv_vardecl (free : SS.t) (bound : SS.t) = function
	| (_,id,_) when (SS.mem id bound) -> 
		raise (Invalid_argument (sprintf "Identifier '%s' will shadow another locally declared variable." id))
		(* Als id in "free" zit, dan overschrijf je een globale variabele met een locale. Dat is ok. *)
	| (_,id,exp) ->
		let newbound = SS.add id bound in 
		fv_exp free newbound exp, newbound;;

let fv_vardecl_list free bound vardecls = 
	List.fold_left
		(fun (beginfree,beginbound) vardecl -> 
		fv_vardecl beginfree beginbound vardecl)
	(free,bound) vardecls;; 

let fv_fundecl free bound (id, fargs, _, vardecllist, stmtlist) =
	let (newfree, newbound) = fv_vardecl_list free (SS.add id bound) vardecllist in
	fv_stmt_list newfree newbound stmtlist;;

let fv_decl = function
	| Vardecl vardecl -> fst (fv_vardecl SS.empty SS.empty vardecl)
	| Fundecl fundecl -> fv_fundecl SS.empty SS.empty fundecl;;

let rec fv_spl graph = function
	| [] -> Success graph
	| decl::decllist ->
		(match fv_decl decl with
		| Error e -> Error e
		| Success (id, needed) ->
			(let rec make_edges graph = function
				| [] -> graph
				| n::ns -> make_edges (add_e id n graph) ns in
			fv_spl (add_v id (Some decl) (make_edges graph needed)) decllist));;

let make_graph spl = fv_spl {v = []; e = []} spl;;