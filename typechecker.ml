open Typechecker_lib
open Typechecker_types
open Typechecker_print
open Types
open Char_func
open Printf
open Graph_make
open Graph_cycles
open Type_graph

(* Env: (x,a,t) ? *)
let m_field env var = function
	| Hd -> fresh; u ((Imp (Lis (Var !v), (Var !v))), var)
	| Tl -> fresh; u ((Imp (Lis (Var !v), Lis (Var !v))), var)
	| Fst -> 
		fresh;
		(let a1 = Var !v in
		fresh;
		u ((Imp (Tup (a1, (Var !v)), a1)), var))
	| Snd ->
		fresh;
		(let a1 = Var !v in
		fresh;
		u ((Imp (Tup (a1, (Var !v)), (Var !v))), var));;

let m_id_var env var id =
	try
		let el = env_var_find id (fst env) in
		u (el.t, var)
	with
	| _ -> Error (sprintf "Variable '%s' not found in environment." id);;

let m_id_fun env var id = 
	try
		let el = env_fun_find id (snd env) in
		let subs = SS.fold (fun x rw -> fresh; RW.add (x, Var !v) rw) el.bound RW.empty in
		u (substitute subs el.t, var)
	with
	| _ -> Error (sprintf "Function '%s' not found in environment." id);;

let rec m_fieldexp env var = function
	| Nofield id -> m_id_var env var id
	| Field (fieldexp, field) ->
		fresh;
		let a = Var !v in
		match m_field env (Imp (a, var)) field with
		| Error e -> Error ("Field ill-typed because of:\n" ^ e)
		| Success x ->
			match m_fieldexp (substitute_env x env) (substitute x a) fieldexp with
			| Error e -> Error ("Field cannot be applied to expression because of:\n" ^ e)
			| Success res1 -> Success (o res1 x);;

let rec m_exp env var = function
	| Exp_int _ -> u (Int, var)
	| Exp_bool _ -> u (Bool, var)
	| Exp_char _ -> u (Char, var)
	| Exp_emptylist -> fresh; u (Lis (Var !v), var)
	| Exp_tuple (e1, e2) -> fresh;
		let a1 = Var !v in
		(match m_exp env a1 e1 with
		| Error e -> Error ("Left ill-typed because of:\n" ^ e)
		| Success x1 -> fresh;
			let a2 = Var !v in
			match m_exp (substitute_env x1 env) a2 e2 with
			| Error e -> Error ("Right ill-typed because of:\n" ^ e)
			| Success res1 ->
				let x = o res1 x1 in
				match u (substitute x (Tup (a1, a2)), substitute x var) with
				| Error e -> Error ("Tuple ill-typed because of:\n" ^ e)
				| Success res2 -> Success (o res2 x))
	| Exp_prefix (op, e1) ->
		(let typeRES = op1_to_subs op in
		(match m_exp env typeRES e1 with
		| Success x ->
			(match u (typeRES, (substitute x var)) with
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
					(match u ((substitute x typeRES), (substitute x var)) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)))
	| Exp_field fieldexp -> m_fieldexp env var fieldexp
	| Exp_function_call (id, args) ->
		try
			let el = env_fun_find id (snd env) in
  	  let rec match_type arglist = function
  			| Imp (argtype1,resttype) ->
  				(match arglist with
  				| [] -> Error "Too few arguments."
  				| arg1::rest ->
  					match m_exp env argtype1 arg1 with
  					| Error e -> Error ("Argument not matching:\n" ^ e)
						| Success x ->
  						match match_type rest resttype with
  						| Error e -> Error e
							| Success res1 -> Success (o res1 x))
  			| rettype ->
  				match arglist with
  				| [] -> u (rettype, var)
  				| _ -> Error "Too many arguments." in
			match_type args el.t
		with
		| _ -> Error (sprintf "Identifier '%s' not found." id);;

let rec m_stmts env var = function
	| [] -> Error "No statement found."
	| [stmt] ->
		(match m_stmt env var stmt with
		| Error e -> Error (sprintf "Second return detected, type of first return ('%s') expected everywhere else:\n%s" (string_of_type var) e)
		| res -> res)
	| stmt::rest ->
		match m_stmt env var stmt with
		| Error e -> Error e
		| Success x ->
			match m_stmts (substitute_env x env) (substitute x var) rest with
			| Error e -> Error e
			| Success res -> Success (o res x)
and m_stmt env var = function
	| Stmt_return None -> u (Void, var)
	| Stmt_return (Some exp) -> m_exp env var exp
	| Stmt_function_call (id,args) ->
		(try 
			let el = env_fun_find id (snd env) in
			let rec get_rettype = function
				| Imp (_,rest) -> get_rettype rest
				| rettype -> rettype in
			m_exp env (get_rettype el.t) (Exp_function_call (id,args))
		with
		| _ -> Error (sprintf "Identifier '%s' not found." id))
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
	| Stmt_define (fieldexp,exp) -> fresh;
		let a = Var !v in
		match m_fieldexp env a fieldexp with
		| Error e -> Error e
		| Success x ->
			match m_exp (substitute_env x env) (substitute x a) exp with
			| Error e -> Error ("Assignment ill-typed:\n" ^ e)
			| Success res -> Success (o res x);;

(* Wat doet deze nou precies? *)
(* In het geval van een vardecl *)
(* levert deze een nieuwe environment: *)
(* - waaraan deze variabele is toegevoegd. *)
(* In het geval van een fundecl *)
(* levert deze een nieuwe environment: *)
(* - waaraan de functie is toegevoegd *)
(* - met het juiste type *)
(* - met de types die gebonden zijn door variabelen *)
(* - met de locale variabelen die door de argumenten zijn gedeclareerd *)
let rec m_spl_pretype env var = function
	| Vardecl (pretyped,id,_) ->
		(try
			let el = env_var_find id (fst env) in
			Error (sprintf "Variable '%s' already in environment, with type '%s'." id (string_of_type el.t))
		with
		| _ ->
			match pretyped with
    	| None -> fresh; Success (Env_var.add {id = id; t = Var !v} (fst env), snd env) 
    	| Some typetoken -> Success (Env_var.add {id = id; t = convert_typetoken typetoken} (fst env), snd env))
	| Fundecl (id,fargs,pretyped,_,_) ->
		try
			let el = env_fun_find id (snd env) in
			Error (sprintf "Function '%s' already in environment, with type '%s'." id (string_of_type el.t))
		with
		| _ ->
			if dups fargs
			then 
				Error (sprintf "Function '%s' has some double argument." id)
			else
				let arg_types = ref SS.empty in
				fresh;
				let fun_type = ref (Var !v) in
				let arg_vars = ref Env_var.empty in
				let rec pretyped_args args = function
					| Imp (t, tr) ->
						(match args with
						| [] -> raise (Invalid_argument (sprintf "Too few arguments for function '%s'." id))
						| arg::rest ->
							(match t with Var x -> arg_types := SS.add x !arg_types | _ -> ());
							arg_vars := Env_var.add {id = arg; t = t} !arg_vars; pretyped_args rest tr)
					| t ->
						(match args with
						| [] -> ()
						| _ -> raise (Invalid_argument (sprintf "Too many arguments for function '%s'." id))) in
				let rec nontyped_args = function
					| [] -> Env_var.empty
					| arg::rest -> 
						fresh; 
						fun_type := Imp (Var !v, !fun_type);
						arg_types := SS.add !v !arg_types;
						Env_var.union (Env_var.singleton {id = arg; t = Var !v}) (nontyped_args rest) in
				let do_everything = 
					match pretyped with
  				| Some t ->
  					pretyped_args fargs (make_type t);
  					fun_type := (make_type t);
  				| None ->
  					arg_vars := nontyped_args fargs; in
				do_everything;			
				Success (fst env, Env_fun.add {id = id; bound = !arg_types; t = !fun_type; locals = !arg_vars} (snd env));;

let rec m_spl env var = function
	| Vardecl (pretyped,id,exp) ->
		(match env_find id env with
			| Error _ -> Error (sprintf "Identifier '%s' not found in environment." id)
			| Success el -> m_exp env el.t exp)
	| Fundecl (id,fargs,pretyped,vardecls,stmts) ->
		(match env_find id env with
		| Error _ -> Error (sprintf "Identifier '%s' not found in environment." id)
		| Success el ->
			(let rec m_vardecls env' var' = function
				| [] -> Success []
				| (tt,varid,exp)::vdecls ->
					(match env_find varid env' with
					| Success _ -> Error (sprintf "Identifier '%s' already declared." varid)
					| Error _ ->
						(let vartype = 
							(match tt with
							| None -> fresh; Var !v
							| Some typetoken -> convert_typetoken typetoken) in
						(let localvar = {id = varid; forall = []; t = vartype; locals = None} in
						env' := localvar::!env';
						(match m_exp env' vartype exp with
						| Error e -> Error e
						| Success x ->
							el.locals <- Some (localvar::(test el.locals));
							(match m_vardecls (substitute_list x env') (substitute x var) vdecls with
							| Error e -> Error e
							| Success res -> Success (o res x))))))	in
			(let env' = ref !env in
			(match m_vardecls env' var vardecls with
			| Error e -> Error e
			| Success x ->
				(match m_stmts (substitute_list x env') (substitute x var) stmts with
				| Error e -> Error e
				| Success res -> Success (o res x))))));;

let rec m_scc env var = function
	| [] -> Success []
	| vertex::scc ->
		match vertex.spl_decl with
		| None -> Error (sprintf "There is never a declaration for '%s'." vertex.id)
		| Some decl ->
			match m_spl_type env var decl with
			| Error e -> Error e
			| Success x ->
				match m_scc (substitute_list x env) (substitute x var) scc with
				| Error e -> Error e
				| Success res1 ->
					(let x1 = o res1 x in
					match m_spl (substitute_list x1 env) (substitute x1 var) decl with
					| Error e -> Error e
					| Success res2 -> Success (o res2 x1));;

let rec m_sccs env var = function
	| [] -> Success (ref [])
	| scc::sccs ->
		let restenv = List.map (fun y -> fresh; {id = y.id; forall = []; t = Var !v; locals = (test_decl y.spl_decl)}) scc in
		match find_dups !env restenv with
		| [] ->
			fresh;
			(match m_scc (ref (List.append !env restenv)) (Var !v) scc with
			| Error e -> Error e
			| Success xn ->
				(let envrest' = List.map (fun (el : env_val) ->
					(let b = substract (tv (substitute xn el.t)) (tv_list (substitute_list xn env)) in
					{id = el.id; forall = b; t = substitute xn el.t; locals = el.locals})) restenv in
				env := List.append !env envrest';
				(match m_sccs (substitute_list xn env) (substitute xn var) sccs with
				| Error e -> Error e
				| Success res1 -> Success env)))
		| list -> Error (sprintf "The following variables have multiple assignments:\n%s" (print_list list));; 

let m env exp = 
  match make_graph exp with
  | Error e -> Error e
  | Success graph -> m_sccs env (Var "0") (tarjan graph);;