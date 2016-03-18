open Typechecker_lib
open Types
open Char_func
open Printf

(* Env: (x,a,t) ? *)
let rec m env exp = function
	| var -> m_exp env var exp
and m_exp env var = function
	| Exp_int _ -> u Int var
	| Exp_bool _ -> u Bool var
	| Exp_char _ -> u Char var
	| Exp_emptylist -> fresh(); u var (Lis (Var !v))
	| Exp_infix (e1, op, e2) ->
		(match op with
		| Listop ->
			fresh();
			(match m env e1 (Var !v) with
			| Success x1 ->
				(match m (substitute x1 env) e2 (Lis (substitute x1 (Var !v))) with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x var) (substitute x (Lis (Var !v))) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("List ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Tail ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Head ill-typed because of:\n" ^ e))
		| Logop _ ->
			(match m env e1 Bool with
			| Success x1 ->
				(match m (substitute x1 env) e2 Bool with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x var) Bool with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Expression not a boolean because of:\n" ^ e))) 
				| Error e -> Error ("Second part of expression not a boolean because of:\n" ^ e))
			| Error e -> Error ("First part of expression not a boolean because of:\n" ^ e))
		| _ -> Error "Operator not supported yet.")
	| _ -> Error "Unsupported expression";;

match (m Int (Exp_infix (Exp_bool true, Listop, (Exp_infix (Exp_bool false, Listop, Exp_emptylist)))) (Var "b")) with
| Success x -> print_subs stdout x;
| Error e -> print_string e;;