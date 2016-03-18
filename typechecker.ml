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
and m_exp env var = function
	| Exp_int _ -> u Int var
	| Exp_bool _ -> u Bool var
	| Exp_char _ -> u Char var
	| Exp_emptylist -> fresh(); u var (Lis (Var !v))
	| Exp_infix (e1, op, e2) ->
		(let (opL, opR, opRES) = op2_to_subs op in
		(match m env e1 opL with
			| Success x1 ->
				(match m (substitute_list x1 env) e2 (substitute x1 opR) with
				| Success res1 ->
					(let x = o res1 x1 in
					(match u (substitute x var) (substitute x opRES) with
					| Success res2 -> Success (o res2 x)
					| Error e -> Error ("Complete expression ill-typed because of:\n" ^ e)))
				| Error e -> Error ("Right part ill-typed because of:\n" ^ e))
			|	Error e -> Error ("Left part ill-typed because of:\n" ^ e)))
	| Exp_prefix (op, e1) ->
		(let opRES = op1_to_subs op in
		(match m env e1 opRES with
		| Success x ->
			(match u (substitute x var) opRES with
			| Success res1 -> Success (o res1 x)
			| Error e -> Error ("Negative ill-typed because of:\n" ^ e))
		| Error e -> Error ("Value ill-typed because of:\n" ^ e)))
	| Exp_tuple (e1, e2) ->
		fresh();
		(let a1 = (Var !v) in
		(match m env e1 a1 with
		| Success x1 ->
			fresh();
			(let a2 = (Var !v) in
			(match m (substitute_list x1 env) e2 a2 with
			| Success res1 ->
				(let x = o res1 x1 in
				(match u (substitute x var) (substitute x (Tup (a1, a2))) with
				| Success res2 -> Success (o res2 x)
				| Error e -> Error ("Tuple ill-typed because of:\n" ^ e)))
			| Error e -> Error ("Right ill-typed because of:\n" ^ e)))
		| Error e -> Error ("Left ill-typed because of:\n" ^ e)))
	| _ -> Error "Unsupported expression";;

match (m [] (Exp_tuple (Exp_bool true, Exp_char 'a')) (Var "b")) with
| Success x -> print_subs stdout x
| Error e -> print_string e;;