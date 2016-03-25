open Typechecker_lib
open Types
open Char_func
open Printf

(* Env: (x,a,t) ? *)
let rec m env exp = function
	| var -> m_exp env var exp
and m_field env var = function
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
		u (Imp (Tup (a1, (Var !v)), (Var !v))) var)
and m_id env var = function
	| Id s ->
		(match env_find (Var s) env with
		| Success (bound, t) ->
			(let rec rewritables list = function
				| [] -> List.rev list
				| a::rest ->
					fresh();
					rewritables ((a,(Var !v))::list) rest in
			u (substitute (rewritables [] bound) t) var)
		| Error _ -> Error (sprintf "Variable '%s' not found in environment." s))
and m_fieldexp env var = function
	| Nofield id -> m_id env var id
	| Field (fieldexp, field) ->
		fresh();
		(let a = Var !v in
		(match m_field env (Imp (a, var)) field with
		| Success x ->
			(match m_fieldexp (substitute_list x env) (substitute x a) fieldexp with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Field cannot be applied to expression because of:\n" ^ e))
		| Error e -> Error ("Field ill-typed because of:\n" ^ e))) 
and m_exp env var = function
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
				(match u (substitute x var) (substitute x (Tup (a1, a2))) with
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
			(match env_find a function_subs with
			| Success (Imp (arg_types, rettype)) ->
				(let rec mawf arg_list (*arg_types*) = function
					| Imp (left,right) ->
						(match arg_list with
						| [] -> Error "Too few arguments."
						| [a] -> Error "Too few arguments."
						| _ ->
							(match mawf (first arg_list) left with
							| Success x ->
								(match m_exp (substitute_list x env) right (last arg_list) with
								| Success res -> Success (o (o function_subs res) x)
								| Error e -> Error ("Argument not matching:\n" ^ e))
							| Error e -> Error ("Deeper argumenttyper says:\n" ^ e)))
					| arg_type ->
						(match arg_list with
						| [] -> Error "Too few arguments."
						| [a] -> m_exp env arg_type a
						| _ -> Error "Too many arguments.") in
				(match mawf args arg_types with
				| Success x ->
					(match u rettype var with
					| Success res -> Success (o res x)
					| Error e -> Error ("Return value ill-typed:\n" ^ e))
				| Error e -> Error ("Argumenttyper says:\n" ^ e)))
			| Success rettype ->
				(match args with
				| [] -> u rettype var
				| _ -> Error "Too many arguments." )
			| Error _ -> Error "This shouldn't happen.")
		| Error e -> Error ("Function ill-typed:\n" ^ e)));;

match (m [("a",([],Imp(Imp(Bool,Int),Void)))] (Exp_function_call (Id "a", [Exp_bool true; Exp_infix (Exp_int 3, Weakop Plus, Exp_int 3)])) (Var "b")) with
| Success x -> print_subs stdout x
| Error e -> print_string e;;