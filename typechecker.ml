open Typechecker_lib
open Types
open Char_func
open Printf
open Spl_to_graph
open Cycledetection
open Type_graph

(* Env: (x,a,t) ? *)
let m_field env var = function
	| Hd -> fresh(); u (Imp (Lis (Var !v), (Var !v))) var
	| Tl -> fresh(); u (Imp (Lis (Var !v), Lis (Var !v))) var
	| Fst -> 
		fresh();
		(let a1 = Var !v in
		fresh();
		u (Imp (Tup (a1, (Var !v)), a1)) var)
	| Snd ->
		fresh();
		(let a1 = Var !v in
		fresh();
		u (Imp (Tup (a1, (Var !v)), (Var !v))) var);;

let m_id env var s =
	(match env_find s env with
	| Success record ->
		(let rec r = function
			| [] -> []
			| x::xs -> fresh(); (x, Var !v)::(r xs) in
		u (substitute (r record.forall) record.t) var)
	| Error _ -> Error (sprintf "Variable '%s' not found in environment." s));;

let rec m_fieldexp env var = function
	| Nofield id -> m_id env var id
	| Field (fieldexp, field) ->
		fresh();
		(let a = Var !v in
		(match m_field env (Imp (a, var)) field with
		| Success x ->
			(match m_fieldexp (substitute_list x env) (substitute x a) fieldexp with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Field cannot be applied to expression because of:\n" ^ e))
		| Error e -> Error ("Field ill-typed because of:\n" ^ e)));;

let rec m_exp env var = function
	| Exp_int _ -> u Int var
	| Exp_bool _ -> u Bool var
	| Exp_char _ -> u Char var
	| Exp_emptylist ->
		fresh();
		u (Lis (Var !v)) var
	| Exp_tuple (e1, e2) ->
		fresh();
		(let a1 = (Var !v) in
		(match m_exp env a1 e1 with
		| Success x1 ->
			fresh();
			(let a2 = (Var !v) in
			(match m_exp (substitute_list x1 env) a2 e2 with
			| Success res1 ->
				(let x = o res1 x1 in
				(match u (substitute x (Tup (a1, a2))) (substitute x var) with
				| Success res2 -> Success (o res2 x)
				| Error e -> Error ("Tuple ill-typed because of:\n" ^ e)))
			| Error e -> Error ("Right ill-typed because of:\n" ^ e)))
		| Error e -> Error ("Left ill-typed because of:\n" ^ e)))
	| Exp_prefix (op, e1) ->
		(let typeRES = op1_to_subs op in
		(match m_exp env typeRES e1 with
		| Success x ->
			(match u typeRES (substitute x var) with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Negative ill-typed because of:\n" ^ e))
		| Error e -> Error ("Value ill-typed because of:\n" ^ e)))
	| Exp_infix (e1, op, e2) ->
		(let (typeL, typeR, typeRES) = op2_to_subs op in
		(match m_exp env typeL e1 with
			| Success x1 ->
				(match m_exp (substitute_list x1 env) (substitute x1 typeR) e2 with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x typeRES) (substitute x var) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)))
	| Exp_field fieldexp -> m_fieldexp env var fieldexp
	| Exp_function_call (id, args) ->
		fresh();
		(let a = Var !v in
		(match m_id env a id with
		| Success function_subs ->
			(match substitute function_subs a with
			| t ->
				(let rec match_type list = function
				| Imp (argtype1,resttype) ->
					(match list with
					| [] -> Error "Too few arguments."
					| arg1::rest ->
						(match m_exp env argtype1 arg1 with
						| Success x ->
							(match match_type rest resttype with
							| Success res1 -> Success (o res1 x)
							| Error e -> Error e)
						| Error e -> Error ("Argument not matching:\n" ^ e)))
				| rettype ->
					(match list with
					| [] -> u rettype var
					| _ -> Error "Too many arguments.") in
				match_type args t))
		| Error e -> Error ("Function ill-typed:\n" ^ e)));;

let rec m_stmts env var = function
	| [] -> Error "No statement found."
	| [stmt] -> 
		(match m_stmt env var stmt with
		| Error e -> Error (sprintf "Second return detected, type of first return ('%s') expected everywhere else:\n%s" (string_of_type var) e)
		| res -> res)
	| stmt::rest ->
		(match m_stmt env var stmt with
		| Success x ->
			(match m_stmts (substitute_list x env) (substitute x var) rest with
			| Success res -> Success (o res x)
			| Error e -> Error e)
		| Error e -> Error e)
and m_stmt env var = function
	| Stmt_return None -> u Void var
	| Stmt_return (Some exp) -> m_exp env var exp
	| Stmt_function_call (id,args) ->
		fresh(); (* HIER: moet afhangen van return type van id? *)
		m_exp env (Var !v) (Exp_function_call (id,args))
	| Stmt_while (exp,stmts) ->
		(match m_stmts env var stmts with
		| Success x ->
			(match m_exp (substitute_list x env) Bool exp with
			| Success res -> Success (o res x)
			| Error e -> Error ("Condition not a boolean:\n" ^ e))
		| Error e -> Error ("Body of 'while' ill-typed:\n" ^ e))
	| Stmt_if (exp,stmts) ->
		(match m_stmts env var stmts with
		| Success x ->
			(match m_exp (substitute_list x env) Bool exp with
			| Success res -> Success (o res x)
			| Error e -> Error ("Condition not a boolean:\n" ^ e))
		| Error e -> Error ("Body of 'then' ill-typed:\n" ^ e))
	| Stmt_if_else (exp,stmts1,stmts2) ->
		(match m_stmts env var stmts1 with
		| Success x1 ->
			(match m_stmts (substitute_list x1 env) (substitute x1 var) stmts2 with
			| Success res1 ->
				(let x = o res1 x1 in
				(match m_exp (substitute_list x env) Bool exp with
  			| Success res -> Success (o res x)
  			| Error e -> Error ("Condition not a boolean:\n" ^ e)))
			| Error e -> Error ("Body of 'else' ill-typed:\n" ^ e))
		| Error e -> Error ("Body of 'then' ill-typed:\n" ^ e))
	| Stmt_define (fieldexp,exp) ->
		fresh();
		(let a = Var !v in
		(match m_fieldexp env a fieldexp with
		| Success x ->
			(match m_exp (substitute_list x env) (substitute x a) exp with
			| Success res -> Success (o res x)
			| Error e -> Error ("Assignment ill-typed:\n" ^ e))
		| Error e -> Error e));;

let rec type_fargs env original_type pretype (*fargs*) = function
	| [] ->
		(match pretype with
		| None -> Success []
		| Some ([],rettype) -> u original_type (convert_rettype rettype)
		| Some (_,_) -> Error "Too few arguments.")
	| farg::fargs ->
		(match pretype with
		| None ->
			fresh();
			env.e <- {id = farg; forall = []; t = Var !v}::env.e;
			type_fargs env original_type pretype fargs
		| Some ([],rettype) -> Error "Too many arguments."
		| Some (type1::types,rettype) ->
			env.e <- {id = farg; forall = []; t = convert_typetoken type1}::env.e;
			type_fargs env original_type (Some (types,rettype)) fargs);;

let rec m_spl (env : environment) var = function
	| Vardecl (pretyped,id,exp) ->
		(match env_find id env with
			| Error _ -> Error (sprintf "Identifier '%s' not found in environment." id)
			| Success el ->
				(let gettype = function
      	| None -> Success []
      	| Some typetoken -> u el.t (convert_typetoken typetoken) in
				(match gettype pretyped with
				| Error e -> Error e
				| Success r -> m_exp (substitute_list r env) (substitute r el.t) exp)))
	| Fundecl (id,fargs,pretyped,vardecls,stmts) ->
		(match env_find id env with
		| Error _ -> Error (sprintf "Identifier '%s' not found in environment." id)
		| Success el ->
			(match el.t with
			| Var elt ->
				(match type_fargs env elt pretyped fargs with
				| Error e -> Error (sprintf "Error while typing arguments for function '%s':\n'%s'" id e)
				| Success x ->
				(let rec m_vardecls env' var' (*vardecls*) = function
					| [] -> Success []
					| (tt,varid,exp)::vdecls ->
						(match env_find varid env' with
						| Success _ -> Error (sprintf "Identifier '%s' already declared." varid)
						| Error _ ->
							(let vartype = 
								(match tt with
  							| None -> fresh(); Var !v
  							| Some typetoken -> convert_typetoken typetoken
								) in
							env'.e <- {id = varid; forall = []; t = vartype}::env'.e;
							(match m_exp env' vartype exp with
							| Error e -> Error e
							| Success x -> m_vardecls (substitute_list x env') (substitute x var) rest
							)
							)
						)
					in
				(let env' = {e = env.e} in
				(match m_vardecls (substitute_list x env') (substitute x var) vardecls with
				| Error e -> Error e
				| Success x2 ->
					(match m_stmts (substitute_list x2 env') (substitute x2 var) stmts with
					| Error e -> Error e
					| Success res -> Success (o res (o x x2))
					)
				)
				)
				)
				)
				)
			| _ -> Error "Weird-ass type."
			);;

let rec m_scc env var = function
	| [] -> Success []
	| vertex::scc ->
		match vertex.spl_decl with
		| None -> Error (sprintf "Unknown identifier '%s'." vertex.id)
		| Some decl ->
			match m_spl env var decl with
			| Error e -> Error e
			| Success x ->
				match m_scc (substitute_list x env) (substitute x var) scc with
				| Error e -> Error e
				| Success res1 -> Success (o res1 x);;

let rec m_sccs (env : environment) var = function
	| [] -> Success []
	| scc::sccs ->
		let restenv = List.map (fun y -> fresh(); {id = y.id; forall = []; t = Var !v}) scc in
		match find_dups env.e restenv with
		| [] ->
			fresh();
			(match m_scc {e = List.append env.e restenv} (Var !v) scc with
			| Error e -> Error e
			| Success xn ->
				(let envrest' = List.map (fun (el : env_val) ->
					(let b = substract (tv (substitute xn el.t)) (tv_list (substitute_list xn env)) in
					{id = el.id; forall = b; t = substitute xn el.t})) restenv in
				(match m_sccs (substitute_list xn {e = List.append env.e envrest'}) (substitute xn var) sccs with
				| Error e -> Error e
				| Success res1 -> Success (o res1 xn))))
		| list -> Error (sprintf "The following variables have multiple assignments:\n%s" (print_list list));; 

let rec toString = function
	| [] -> ""
	| [scc] ->
		(let rec helper = function
			| [] -> ""
			| [x] -> x.id
			| x::xs -> sprintf "%s, %s" (x.id) (helper xs) in
		sprintf "[%s]" (helper scc))
	| scc::rest -> sprintf "%s,\n%s" (toString [scc]) (toString rest);;

let m env exp = 
  match make_graph exp with
  | Error e -> Error e
  | Success graph -> m_sccs env (Var "0") (tarjan graph);;