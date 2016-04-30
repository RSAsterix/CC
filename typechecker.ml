open Typechecker_lib
open Typechecker_types
open Typechecker_print
open Types
open Char_func
open Printf

(* Env: (x,a,t) ? *)
let m_field env var = function
	| Hd -> fresh(); u (var, (Imp (Lis (Var !v), (Var !v))))
	| Tl -> fresh(); u (var, (Imp (Lis (Var !v), Lis (Var !v))))
	| Fst -> 
		fresh();
		let a1 = Var !v in
		fresh();
		u (var, Imp (Tup (a1, (Var !v)), a1))
	| Snd ->
		fresh();
		let a1 = Var !v in
		fresh();
		u (var, Imp (Tup (a1, (Var !v)), (Var !v)));;

let m_id_var env var id =
	try
		let el = env_var_find id env in
		u (var, el.t)
	with
	| _ -> Error (sprintf "Variable '%s' not found in environment." id);;

let m_id_fun env var id = 
	try
		let el = env_fun_find id env in
		let subs = SS.fold (fun x rw -> fresh(); RW.add (x, (Var !v, Env_var.empty)) rw) el.bound RW.empty in
		u (var, substitute subs el.t)
	with
	| _ -> Error (sprintf "Function '%s' not found in environment." id);;

let rec m_fieldexp (env : environment) var = function
	| Nofield id -> m_id_var env var id
	| Field (fieldexp, field) ->
		fresh();
		let a = Var !v in
		match m_field env (Imp (a, var)) field with
		| Error e -> Error ("Field ill-typed because of:\n" ^ e)
		| Success x ->
			match m_fieldexp (substitute_env x env) (substitute x a) fieldexp with
			| Error e -> Error ("Field cannot be applied to expression because of:\n" ^ e)
			| Success res1 -> Success (o res1 x);;

let rec m_exp env var = function
	| Exp_int _ -> u (var, Int)
	| Exp_bool _ -> u (var, Bool)
	| Exp_char _ -> u (var, Char)
	| Exp_emptylist -> fresh(); u (var, Lis (Var !v))
	| Exp_tuple (e1, e2) -> fresh();
		let a1 = Var !v in
		(match m_exp env a1 e1 with
		| Error e -> Error ("Left ill-typed because of:\n" ^ e)
		| Success x1 -> fresh();
			let a2 = Var !v in
			match m_exp (substitute_env x1 env) a2 e2 with
			| Error e -> Error ("Right ill-typed because of:\n" ^ e)
			| Success res1 ->
				let x = o res1 x1 in
				match u (substitute x var, substitute x (Tup (a1, a2))) with
				| Error e -> Error ("Tuple ill-typed because of:\n" ^ e)
				| Success res2 -> Success (o res2 x))
	| Exp_prefix (op, e1) ->
		(let typeRES = op1_to_subs op in
		(match m_exp env typeRES e1 with
		| Success x ->
			(match u (substitute x var, typeRES) with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Negative ill-typed because of:\n" ^ e))
		| Error e -> Error ("Value ill-typed because of:\n" ^ e)))
	| Exp_infix (e1, op, e2) ->
		(let (typeL, typeR, typeRES) = op2_to_subs op in
		(match m_exp env typeL e1 with
			| Success x1 ->
				(match m_exp (substitute_env x1 env) (substitute x1 typeR) e2 with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x var, substitute x typeRES) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)))
	| Exp_field fieldexp -> m_fieldexp env var fieldexp
	| Exp_function_call (id, args) ->
		fresh();
		let a = Var !v in
		match m_id_fun env a id with
		| Error e -> Error (sprintf "Identifier '%s' not found." id)
		| Success xa ->
			let elt = substitute xa a in
		  let rec match_type arglist = function
  			| Imp (argtype1,resttype) ->
  				(match arglist with
  				| [] -> Error "Too few arguments."
  				| arg1::rest ->
  					match m_exp env argtype1 arg1 with
  					| Error e -> Error ("Argument not matching:\n" ^ e)
						| Success x ->
  						match match_type rest (substitute x resttype) with
  						| Error e -> Error e
							| Success res1 -> 
								let new_res = RW.fold (fun y rw -> RW.add (fst y, (substitute x (fst (snd y)), substitute_vars x (snd (snd y)))) rw) res1 RW.empty in
								Success new_res)
  			| rettype ->
  				match arglist with
  				| [] -> u (var, rettype)
  				| _ -> Error "Too many arguments." in
			match_type args elt;;

let rec m_stmts env var = function
	| [] -> Error "No statement found."
	| [stmt] ->
		(match m_stmt env var stmt with
		| Error e -> Error (sprintf "Master type '%s' cannot be unified anymore:\n%s" (string_of_type var) e)
		| res -> res)
	| stmt::rest ->
		match m_stmt env var stmt with
		| Error e -> Error e
		| Success x ->
			match m_stmts (substitute_env x env) (substitute x var) rest with
			| Error e -> Error e
			| Success res -> Success (o res x)
and m_stmt env var = function
	| Stmt_return None -> u (var, Void)
	| Stmt_return (Some exp) -> m_exp env var exp
	| Stmt_function_call (id,args) ->
		fresh();
		m_exp env (Var !v) (Exp_function_call (id,args))
	| Stmt_while (exp,stmts) ->
		(match m_stmts env var stmts with
		| Error e -> Error ("Body of 'while' ill-typed:\n" ^ e)
		| Success x ->
			match m_exp (substitute_env x env) Bool exp with
			| Error e -> Error ("Condition not a boolean:\n" ^ e)
			| Success res -> Success (o res x))
	| Stmt_if (exp,stmts) ->
		(match m_stmts env var stmts with
		| Error e -> Error ("Body of 'then' ill-typed:\n" ^ e)
		| Success x ->
			match m_exp (substitute_env x env) Bool exp with
			| Error e -> Error ("Condition not a boolean:\n" ^ e)
			| Success res -> Success (o res x))
	| Stmt_if_else (exp,stmts1,stmts2) ->
		(match m_stmts env var stmts1 with
		| Error e -> Error ("Body of 'then' ill-typed:\n" ^ e)
		| Success x1 ->
			match m_stmts (substitute_env x1 env) (substitute x1 var) stmts2 with
			| Error e -> Error ("Body of 'else' ill-typed:\n" ^ e)
			| Success res1 ->
				let x = o res1 x1 in
				match m_exp (substitute_env x env) Bool exp with
  			| Error e -> Error ("Condition not a boolean:\n" ^ e)
				| Success res -> Success (o res x))
	| Stmt_define (fieldexp,exp) -> fresh();
		let a = Var !v in
		match m_fieldexp env a fieldexp with
		| Error e -> Error e
		| Success x ->
			match m_exp (substitute_env x env) (substitute x a) exp with
			| Error e -> Error ("Assignment ill-typed:\n" ^ e)
			| Success res -> Success (o res x);;

let rec pretype_fun fargs = function
	| Some (argtypes,rettype as t) -> make_type t
	| None ->
		match fargs with
		| [] -> fresh(); Var !v
		| arg::rest -> fresh();
			let a = Var !v in
		 	Imp (a, pretype_fun rest None);;

let rec pretype_var = function
	| Some t -> convert_typetoken t
	| None -> fresh(); Var !v;; 

let rec type_fargs t = function
	| [] -> 
		(match t with
		| Imp (_,_) -> Error "Too few arguments."
		| t -> Success Env_var.empty)
	| arg::rest ->
		match t with
		| Imp (targ,trest) ->
			(match type_fargs trest rest with
			| Error e -> Error e
			| Success resttype -> 
				try
					Success (Env_var.add {id = arg; t = targ} resttype)
				with
				| _ -> Error (sprintf "Argument '%s' already in environment." arg))
		| t -> Error "Too many arguments.";;		

let rec new_env = function
	| [] -> Env.empty
	| (Fundecl (id,fargs,pretype,_,_))::scc ->
		let t = pretype_fun fargs pretype in
		let xa = {id = id; bound = SS.empty; t = t; locals = Env_var.empty} in
		Env.add_fun xa (new_env scc)
	| (Vardecl (pretype,id,_))::scc ->
		let t = pretype_var pretype in
		let xa = {id = id; t = t} in
		Env.add_var xa (new_env scc);;

let m_vardecl env var (pretype,id,exp) =
	fresh();
	let a = Var !v in
	match m_id_var env a id with
	| Error e -> Error (sprintf "Variable '%s' not found." id)
	| Success x ->
		match m_exp (substitute_env x env) (substitute x a) exp with
		| Error e -> Error (sprintf "In '%s':\n%s" id e)
		| Success res -> Success (o res x);;

let m_fundecl env var (id,fargs,pretype,vardecls,stmts) = 
	fresh();
	let a = Var !v in
	match m_id_fun env a id with
	| Error e -> Error (sprintf "Function '%s' not found." id)
	| Success xa ->
		let elt = (substitute xa a) in
		match type_fargs elt fargs with
		| Error e -> Error (sprintf "Error in '%s':\n%s" id e)
		| Success arg_vars ->
			let newenv = Env.add_locals arg_vars env in
			let rec m_vardecls localenv var = function
			| [] -> 
				let locals = Env_var.diff (fst localenv) (fst env) in
				Success (RW.singleton (id, (elt, locals)))
			| vardecl::rest ->
				fresh();
				let newvar = {id = get_id vardecl; t = Var !v} in
				try
					let localenv = Env.add_var newvar localenv in
					let locals = Env_var.diff (fst localenv) (fst env) in
					let x1 = (RW.singleton (id, (elt, locals))) in
					match m_vardecl (substitute_env x1 localenv) var vardecl with
					| Error e -> Error e
					| Success x ->
						let x = o x1 x in
						match m_vardecls (substitute_env x localenv) (substitute x var) rest with
						| Error e -> Error e
						| Success res -> Success (o res x)
				with
				| _ -> Error (sprintf "Local variable '%s' already local." id) in 
			match m_vardecls newenv var vardecls with
			| Error e -> Error (sprintf "In '%s':\n%s" id e)
			| Success x ->
				match m_stmts (substitute_env x newenv) (returntype elt) stmts with
				| Error e -> Error (sprintf "In '%s':\n%s" id e)
				| Success res -> Success (o res x);;
		
let rec m_spl env var = function
	| [] -> Success RW.empty
	| (Vardecl vardecl)::rest ->
		(match m_vardecl env var vardecl with
		| Error e -> Error e
		| Success x1 ->
			match m_spl (substitute_env x1 env) (substitute x1 var) rest with
			| Error e -> Error e
			| Success res -> Success (o res x1))
	| (Fundecl fundecl)::rest ->
		match m_fundecl env var fundecl with
		| Error e -> Error e
		| Success x1 ->
			match m_spl (substitute_env x1 env) (substitute x1 var) rest with
			| Error e -> Error e
			| Success res -> Success (o res x1);;

let m exp =
  try 
		let env = new_env exp in
		match m_spl env (Var "0") exp with
		| Error e -> Error e
		| Success r -> Success (substitute_env r env)
	with
	| Invalid_argument e -> Error e;;