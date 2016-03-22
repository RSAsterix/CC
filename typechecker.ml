open Typechecker_lib
open Types
open Char_func
open Printf

(* Env: (x,a,t) ? *)
let rec m env exp = function
	| var -> m_exp env var exp
and m_field env var = function
	| Hd -> fresh(); u var (Imp (Lis (Var !v), (Var !v)))
	| Tl -> fresh(); u var (Imp (Lis (Var !v), Lis (Var !v)))
	| Fst -> 
		fresh();
		(let a1 = Var !v in
		fresh();
		u var (Imp (Tup (a1, (Var !v)), a1)))
	| Snd ->
		fresh();
		(let a1 = Var !v in
		fresh();
		u var (Imp (Tup (a1, (Var !v)), (Var !v))))
and m_id env var = function
	| Id s ->
		(match env_find s env with
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
		u var (Lis (Var !v))
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
		(let opRES = op1_to_subs op in
		(match m_exp env opRES e1 with
		| Success x ->
			(match u (substitute x var) opRES with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Negative ill-typed because of:\n" ^ e))
		| Error e -> Error ("Value ill-typed because of:\n" ^ e)))
	| Exp_infix (e1, op, e2) ->
		(let (opL, opR, opRES) = op2_to_subs op in
		(match m_exp env opL e1 with
			| Success x1 ->
				(match m_exp (substitute_list x1 env) (substitute x1 opR) e2 with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x opRES) (substitute x var) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)))
	| Exp_field fieldexp -> m_fieldexp env var fieldexp
	| Exp_function_call (id, args) ->
		fresh();
		(let temp = !v in
		(match m_id env (Var temp) id with
		| Success x ->
			(match env_find temp x with
			| Success t ->
				(let unpack a = function
					| Imp (argimp,res) ->
						(match a with
						| [] -> Error "Result is a function."
						| [arg] ->
							(match m_exp (substitute_list x env) (substitute x argimp) arg with
							| Success res1 ->
								(match u res var with
								| Success res2 -> Success (o (o res1 x) res2)
								| Error e -> Error ("Wat gebeurt hier?\n" ^ e))
							| Error e -> Error ("Argument not matching with function type:\n" ^ e))
						| arg::rest -> Error "Jup")
					| res -> Success x in
				unpack (List.rev args) t)
			| Error e -> Error e)
		| Error e -> Error ("Function ill-typed because of:\n" ^ e)));;

match (m [("a",([],Imp(Int,Void)))] (Exp_function_call (Id "a", [Exp_bool true; Exp_infix (Exp_int (Inttoken 3), Weakop Plus, (Exp_int (Inttoken 3)))])) (Var "b")) with
| Success x -> print_subs stdout x
| Error e -> print_string e;;