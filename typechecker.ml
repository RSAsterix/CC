open Typechecker_lib
open Typechecker_types
open Typechecker_print
open Types
open Char_func
open Printf
open Graph_make
open Graph_cycles
open Graph_lib

(* Checks one field *)
let m_field env var = function
	| Hd -> fresh(); u (var, Imp (Lis (Var !v), (Var !v)))
	| Tl -> fresh(); u (var, Imp (Lis (Var !v), Lis (Var !v)))
	| Fst -> fresh(); let a = Var !v in fresh(); u (var, Imp (Tup (a, (Var !v)), a))
	| Snd -> fresh(); let a = Var !v in fresh(); u (var, Imp (Tup (a, (Var !v)), (Var !v)));;

(* Finds the type of a constructor in the environment *)
let m_cons env var cons =
	try
		let el = Env.find_type cons env in
		u (var,el.t)
	with
	| Not_in_env el -> Error (sprintf "Constructor '%s' not found in environment." el);;

(* Finds the type of a variable in the environment *)
let m_id_var env var id =
	try
		let el = Env.find_var id env in
		u (var,el.t)
	with
	| Not_in_env el -> Error (sprintf "Variable '%s' not found in environment." el);;

(* Finds the type of a function in the environment *)
let m_id_fun env var id = 
	try (
		let el = Env.find_fun id env in
		let f = (fun x rw -> 
			fresh(); 
			RW.add (x, Var !v) rw) in
		let x = SS.fold f el.bound RW.empty in
		u (var,substitute x el.t))
	with
	| Not_in_env el -> Error (sprintf "Function '%s' not found in environment." el);;

(* Recursively checks a fieldexpression: *)
(* If it's just a variable, look it up. *)
(* If it's more than that, treat the fields as functions *)
(* and work according to the rule in the college slides. *)
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
			| Success res1 -> Success (o x res1);;

(* Checks expressions according to college slides. *)
(* Interesting parts will be commented upon inline. *)
let rec m_exp env var = function
	| Exp_int _ -> u (var, Int)
	| Exp_bool _ -> u (var, Bool)
	| Exp_char _ -> u (var, Char)
	| Exp_emptylist -> fresh(); u (var, Lis (Var !v))
	| Exp_low_bar -> fresh(); u (var, Var !v)
	| Exp_constructor cons -> m_cons env var cons
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
	(* Operators "Neg" and "Not" have the same code, *)
	(* apart from the type they need matched. *)
	(* TypeRES will be Int for "Neg" and Bool for "Not" *)
	| Exp_prefix (op, e1) ->
		let typeRES = op1_to_subs op in
		(match m_exp env typeRES e1 with
		| Error e -> Error ("Value ill-typed because of:\n" ^ e)
		| Success x ->
			match u (substitute x var, typeRES) with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Negative ill-typed because of:\n" ^ e))
	(* Same story as in "Exp_prefix": *)
	(* Left expression needs to be typeL, *)
	(* Right expression needs to be typeR, *)
	(* Result needs to be typeRES. *) 
	| Exp_infix (e1, op, e2) ->
		let (typeL, typeR, typeRES) = op2_to_subs op in
		(match m_exp env typeL e1 with
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)
			| Success x1 ->
				match m_exp (substitute_env x1 env) (substitute x1 typeR) e2 with
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e)
				| Success res1 ->
					let x = o res1 x1 in
					match u (substitute x var, substitute x typeRES) with
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)
					| Success res2 -> Success (o res2 x))
	| Exp_field fieldexp -> m_fieldexp env var fieldexp
	(* Works about the same as in the college slides, *)
	(* except for the local function "match_type" that *)
	(* gives every argument the correct type, according to *)
	(* the function type found in the environment. *)
	| Exp_function_call (id, args) ->
		fresh();
		let a = Var !v in
		match m_id_fun env a id with
		| Error e -> Error e
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
							| Success res -> Success (o res x))
  			| rettype ->
  				match arglist with
  				| [] -> u (var, rettype)
  				| _ -> Error "Too many arguments." in
			match match_type args elt with
			| Error e -> Error e
			| Success x -> Success (o x xa);;		

(* Recursively checks all statements in a list. *)
let rec m_stmts env var = function
	| [] -> Error "No statement found."
	| [stmt] ->
		(match m_stmt env var stmt with
		| Error e -> Error (sprintf "Master type '%s' cannot be unified anymore:\n%s" (string_of_type var) e)
		| success -> success)
	| stmt::rest ->
		match m_stmt env var stmt with
		| Error e -> Error e
		| Success x ->
			match m_stmts (substitute_env x env) (substitute x var) rest with
			| Error e -> Error e
			| Success res -> Success (o res x)
(* Checks statements according to college slides. *)
(* Interesting parts will be commented upon inline. *)
and m_stmt env var = function
	| Stmt_return None -> u (var, Void)
	| Stmt_return (Some exp) -> m_exp env var exp
	| Stmt_function_call (id,args) -> fresh(); m_exp env (Var !v) (Exp_function_call (id,args))
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
	| Stmt_define (fieldexp,exp) ->
		fresh();
		let a = Var !v in
		(match m_fieldexp env a fieldexp with
		| Error e -> Error e
		| Success x ->
			match m_exp (substitute_env x env) (substitute x a) exp with
			| Error e -> Error ("Assignment ill-typed:\n" ^ e)
			| Success res -> Success (o x res))
	(* Checks the type of the expression the cases need to be matched to. *)
	(* Then, for every case: *)
	(* - It extracts the hyperlocals with the local function "hyperlocals", *)
	(*   and places them in a temporary environment used only for this case; *)
	(* - It checks if the "when"-clause is a Bool; *)
	(* - It checks the statementlist. *)
	| Stmt_match (exp,caselist) ->
		fresh();
		let a = Var !v in
		match m_exp env a exp with
		| Error e -> Error e
		| Success x ->
			(* Local functions for generating a temporary variable environment. *)
			let rec hyperlocals = function
				| Exp_field (Nofield id) -> fresh();
					Success (Env_var.singleton {id = id; t = Var !v})
				| Exp_field _ -> Error "Not allowed to match to a function call (field)."
				| Exp_function_call _ -> Error "Not allowed to match to a function call."
				| Exp_infix (head,Listop,tail) ->
					(match hyperlocals head with
					| Error e -> Error e
					| Success h ->
						match hyperlocals tail with
						| Error e -> Error e
						| Success t -> 
							try 
								Success (Env_var.union_safe h t) 
							with 
							| Already_known e -> Error (sprintf "Duplicate hyperlocal '%s'." e))
				| Exp_prefix (Neg, Exp_int _) -> Success Env_var.empty
				| Exp_prefix _ -> Error "Can't use negation/negative this way."
				| Exp_tuple (left,right) ->
					(match hyperlocals left with
					| Error e -> Error e
					| Success l ->
						match hyperlocals right with
						| Error e -> Error e
						| Success r -> 
							try 
								Success (Env_var.union_safe l r) 
							with 
							| Already_known e -> Error (sprintf "Duplicate hyperlocal '%s'." e))
				| _ -> Success Env_var.empty in
			(* Local function for typechecking a single case. *)
			let m_case env var varexp (mexp,mwhen,mstmts) =
				(match hyperlocals mexp with
				| Error e -> Error e
				| Success hlocals ->
					match m_exp {env with vars = hlocals} varexp mexp with
					| Error e -> Error e
					| Success x_cl ->
						let env' = Env.add_locals hlocals env in
						let m_when = function
							| None -> Success RW.empty
							| Some mwhen -> m_exp (substitute_env x_cl env') Bool mwhen in
						match m_when mwhen with
						| Error e -> Error e
						| Success res_cl ->
							let x1_cl = o res_cl x_cl in
							match m_stmts (substitute_env x1_cl env') (substitute x1_cl var) mstmts with
							| Error e -> Error e
							| Success res2_cl -> Success (o res2_cl x1_cl)) in
			(* Local function for recursively checking a list of cases. *)
			let rec m_caselist env var varexp = function
				| [] -> Error "No match-case found."
				| [mcase] -> m_case env var varexp mcase
				| mcase::cases ->
					(match m_case env var varexp mcase with
					| Error e -> Error e
					| Success x ->
						match m_caselist (substitute_env x env) (substitute x var) (substitute x varexp) cases with
						| Error e -> Error e
						| Success res -> Success (o res x)) in
			match m_caselist (substitute_env x env) (substitute x var) (substitute x a) caselist with
			| Error e -> Error e
			| Success res -> Success (o res x);;

(* If an explicit type is given, convert it to a usable *)
(* typechecker type. *)
(* If not, just take a fresh type variable. *)
let rec pretype_var env = function
	| Some t -> convert_typetoken env t
	| None -> fresh(); Var !v;;

(* Since the variable is already in the environment, *)
(* This only needs to check the expression. *)
let m_vardecl env var (pretype, id, exp) =
	m_exp env var exp;;

(* The type of the function that gets some arguments is in *)
(* the environment already: type_fargs uses that type to give *)
(* all the arguments a valid type. *)
(* If all arguments are typed and the functiontype *)
(* is still an implication, it fails. *)
(* If there are still arguments, but the functiontype *)
(* is not an implication, it fails. *)
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
				Success (Env_var.add {id = arg; t = targ} resttype))
		| t -> Error "Too many arguments.";;

(* Interesting parts will be commented upon inline. *)
let m_fundecl env var (id,fargs,pretype,vardecls,stmts) = 
	(* If there are duplicate arguments, it fails. *)
	if dups fargs
	then Error (sprintf "Function '%s' contains some duplicate argument." id)
	else (		
		fresh();
		let a = Var !v in
		match m_id_fun env a id with
		| Error e -> Error (sprintf "Function '%s' not found." id)
		| Success xa ->
			(* 'elt' will contain the type of the function *)
			(* as found in the environment. *)
			let elt = (substitute xa a) in
			match type_fargs elt fargs with
				| Error e -> Error (sprintf "Error in '%s':\n%s" id e)
				| Success locals ->
					(* This local function will check a list of *)
					(* variable declarations recursively, adding *)
					(* the correctly typed variable to the local *)
					(* environment each time, returning the locals *)
					(* as well as the rewrite rules it found. *)
					let rec m_vardecls locals var = function
  				| [] -> Success (RW.empty, locals)
  				| (vpretype,vid,_ as vardecl)::rest ->
						try (
							let a = pretype_var env vpretype in
    					match m_vardecl (Env.add_locals locals env) a vardecl with
    					| Error e -> Error e
    					| Success x ->
								let newvar = {id = vid; t = a} in
								let locals' = Env_var.add_safe newvar locals in
    						match m_vardecls (substitute_vars x locals') (substitute x var) rest with
    						| Error e -> Error e
    						| Success (res, locals') -> Success (o x res, locals'))
						with
						| Already_known el -> Error (sprintf "Variable '%s' already local in '%s'." el id) in
					match m_vardecls locals var vardecls with
					| Error e -> Error (sprintf "In '%s':\n%s" id e)
					| Success (x, locals) ->
						try (
							let newenv = Env.add_locals locals env in
							(Env.find_fun id newenv).locals <- locals;
							match m_stmts (substitute_env x newenv) (returntype elt) stmts with
  						| Error e -> Error (sprintf "In '%s':\n%s" id e)
  						| Success res -> Success (o res x))
						with
						| Not_in_env el -> Error (sprintf "Function '%s' not found in environment (in '%s')." el id));;

(* This function is explained in the report, *)
(* but not very interesting otherwise. *)
let rec m_scc env var = function
	| [] -> Success (RW.empty)
	| vert::rest ->
		match vert.spl_decl with
		| Vardecl (pretype,id,_ as vardecl) ->
			let a = (Env.find_var id env).t in
  		(match m_vardecl (Env.exclude id env) a vardecl with
  		| Error e -> Error e
  		| Success x1 ->
  			match m_scc (substitute_env x1 env) (substitute x1 var) rest with
  			| Error e -> Error e
  			| Success res -> Success (o res x1))
		| Fundecl fundecl ->
			match m_fundecl env var fundecl with
  		| Error e -> Error e
  		| Success x1 ->
  			match m_scc (substitute_env x1 env) (substitute x1 var) rest with
  			| Error e -> Error e
  			| Success res -> Success (o res x1);;

(* Bound variables only need to be added after checking *)
(* an entire scc. This function handles updating the *)
(* environment after checking an scc. *)
let rec argify env ads xn = function
	| [] -> Env.union ads env
	| vert::scc ->
		match vert.spl_decl with
		| Vardecl (_,id,_) -> 
			let el = Env.find_var id ads in
			let aixn = substitute xn el.t in
			let newel = {el with t = aixn} in
			argify env (Env.update_var newel ads) xn scc
		| Fundecl (id,fargs,_,_,_) ->
			let el = Env.find_fun id ads in
			let aixn = substitute xn el.t in
			let bi = SS.diff (tv aixn) (tv_env env) in
			match type_fargs aixn fargs with
			| Error e -> raise (Invalid_argument e)
			| Success locals ->
				let newel = {el with bound = bi; t = aixn; locals = Env_var.add_locals locals el.locals} in
				argify env (Env.update_fun newel ads) xn scc;;

(* A variable can never be be in a strongly connected component *)
(* that contains more than just that variable: it can never be *)
(* interdependent. *)
let rec check_scc = function
	| [] -> false
	| [_] -> false
	| scc -> List.exists (fun x -> match x.spl_decl with Vardecl _ -> true | _ -> false) scc;;

(* If an explicit type is given, convert it to a usable *)
(* typechecker type for the function and its arguments. *)
(* If not, just take fresh type variables. *)
let rec pretype_fun env fargs = function
	| Some (argtypes,rettype as t) -> make_type env t
	| None ->
		match fargs with
		| [] -> fresh(); Var !v
		| arg::rest -> fresh();
			let a = Var !v in
		 	Imp (a, pretype_fun env rest None);;

(* Create stubs for all functions/variables in a *)
(* strongly connected component. *)
let rec new_env env = function
	| [] -> env
	| vert::scc ->
		match vert.spl_decl with
  	| Fundecl (id,fargs,pretype,_,_) ->
  		let t = pretype_fun env fargs pretype in
  		let xa = {id = id; bound = SS.empty; t = t; locals = Env_var.empty} in
			new_env (Env.add_fun xa env) scc
  	| Vardecl (pretype,id,_) ->
  		let t = pretype_var env pretype in
  		let xa = {id = id; t = t} in
			new_env (Env.add_var xa env) scc;; 

(* Works like explained in college slides. *)
let rec m_sccs env var = function
	| [] -> Success env
	| scc::rest ->
		if check_scc scc
		then Error "Interdependent global variable declarations."
		else (
  		try (
    		let env' = new_env env scc in
    		match m_scc env' var scc with
    		| Error e -> Error e
    		| Success xn ->
    			let envxn = substitute_env xn env in
    			let varxn = substitute xn var in
    			let ads = Env.diff (substitute_env xn env') envxn in
    			let envxn_ads = argify envxn ads xn scc in
    			match m_sccs envxn_ads varxn rest with
    			| Error e -> Error e
    			| Success res -> Success (Env.union envxn_ads res))
  		with
  		| Already_known a -> Error (sprintf "Duplicate declaration: '%s'" a))

(* Places self-defined types in the environment. *)
let rec m_typedecls env = function
	| [] -> env
	| typedecl::rest ->
		match typedecl with
		| Rename (id,tt) -> 
			let env' = Env.add_type {id = id; t = convert_typetoken env tt} env in
			m_typedecls env' rest
		| Enum (id,[]) -> 
			raise (Invalid_argument (sprintf "No type listed for '%s'." id))
		| Enum (id,enum) ->
			(* Simple local function that checks if a constructor is already used somewhere. *)
			(* If not, actually adds them to the environment. *)
			let rec tt_to_enum = function
				| [] -> []
				| e::tl when not ((List.mem e tl) || (Env.exists_cons e env)) -> (e,None)::(tt_to_enum tl)
					(* The following comment is just for Martin and Tom *)
  					(* Hier moet dus straks iets komen om daadwerkelijke constructoren af te handelen *)
  					(* Vergeet niet ook Env.exists_cons en Env.get_cons ofzo te updaten *)
				| e::_ -> raise (Invalid_argument (sprintf "Duplicate typeconstructor '%s'." e)) in
			let env' = Env.add_type {id = id; t = Enum (tt_to_enum enum)} env in
			let rec tt_to_env env'' = function
				| [] -> env''
				| e::tl -> 
					let env'' = Env.add_type {id = e; t = convert_typetoken env' (Type_id id)} env'' in
					tt_to_env env'' tl in
			m_typedecls (tt_to_env env' enum) rest;;

(* Combination of "m_sccs", "m_scc" and "m_fundecl". Checks a few things:
-	main is a function, not a variable
-	main has no arguments
-	main returns an integer *)
let m_main env main = 
	match main.spl_decl with
	| Vardecl _ -> Error "'main' cannot be a variable."
	| Fundecl ((_,fargs,_,_,_) as fundecl) ->
		match fargs with
		| _::_ -> Error "'main' cannot have arguments."
		| _ -> try (
  			let f_main = {id = "$main"; bound = SS.empty; t = Int; locals = Env_var.empty} in
  			let env' = Env.add_fun f_main env in 
  			match m_fundecl env' Int fundecl with
				| Error e -> Error e
				| Success x ->
    			let envxn = substitute_env x env in
    			let ads = Env.diff (substitute_env x env') envxn in
    			Success (argify envxn ads x [main]))
  		with
  		| Already_known a -> Error (sprintf "Duplicate declaration: '%s'" a);;

let m exp =
  try 
		(* Generate a new environment that contains self-defined types. *)
		let env = m_typedecls Env.empty (fst exp) in
		
		(* Make a graph out of the rest of the declarations. *)
		let graph = make_graph (snd exp) in
		
		(* Take the main function out of that graph. *)
		let main = List.find (fun x -> x.id = "$main") graph.v in
		let graph = {graph with v = List.filter (fun x -> not (x.id = "$main")) graph.v} in
		
		(* Typecheck the entire program... *)
		match m_sccs env (Var "0") (tarjan graph) with
		| Success env ->
			(* ...then typecheck the main function. *)
			m_main env main
		| Error e -> Error e
	with
	| Not_found -> Error "No 'main' found."
	| Invalid_argument e -> Error e
	| Already_known e -> Error (sprintf "Duplicate type '%s'." e);;