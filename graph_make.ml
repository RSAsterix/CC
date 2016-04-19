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
and fv_exp_list free bound explist = List.fold_left (fun beginfree exp -> fv_exp beginfree bound exp) free explist;;

let rec fv_stmt free bound = function
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
and fv_stmt_list free bound = function
	| [] -> free
	| stmt::stmts -> fv_stmt_list (fv_stmt free bound stmt) bound stmts;;

let fv_vardecl free bound = function
	| (_,id,_) when (List.mem id bound || List.mem id free) -> Error (sprintf "Identifier '%s' already known." id)
	| (_,id,exp) -> Success (fv_exp free (id::bound) exp, id);;

let rec fv_vardecl_list free bound = function
	| [] -> Success (free, bound)
	| v::vs ->
		match fv_vardecl free bound v with
		| Error e -> Error e
		| Success (free', id) -> fv_vardecl_list free' (id::bound) vs;;

let fv_fundecl free bound = function
	| (id, _, _, _, _) when (List.mem id bound || List.mem id free) -> Error (sprintf "Identifier '%s' already known." id)
	| (id, fargs, _, vardecllist, stmtlist) ->
		match fv_vardecl_list free (List.append fargs (id::bound)) vardecllist with
		| Error e -> Error e
		| Success (free', bound') -> Success (fv_stmt_list free' bound' stmtlist, id);;

let fv_decl = function
	| Vardecl vardecl ->
		(match fv_vardecl [] [] vardecl with
		| Error e -> Error e
		| Success (free, id) -> Success (id,free))
	| Fundecl fundecl ->
		(match fv_fundecl [] [] fundecl with
		| Error e -> Error e
		| Success (free, id) -> Success (id,free));;

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