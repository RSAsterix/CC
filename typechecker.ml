open Typechecker_lib
open Types
open Char_func
open Printf

(* nieuwe variabele genereren *)
let c = ref 0;;
let v = ref "";;
let fresh = function
	| _ -> 
		c := !c + 1;
		v := sprintf "%if" !c;;

(* herschrijfregel uit subs gebruiken   *)
(* subs = [x1 |-> nx1; x2 |-> nx2; ...] *) 
let rec rewrite subs i = 
	match subs with
	| [] -> Var i
	| (x,nx)::xs when (x = i) -> nx
	| (x,nx)::xs -> rewrite xs i;;

(* substitutieregels toepassen *)
let rec substitute subs = function
	| Var i -> rewrite subs i
	| Imp (t1,t2) -> Imp (substitute subs t1, substitute subs t2)
	| Tup (t1,t2) -> Tup (substitute subs t1, substitute subs t2)
	| Lis t -> Lis (substitute subs t)
	| t -> t;;

(* Infix versie van o, vervangt alle substituties in s2 *)
(* volgens de regels in s1 *)
let o s1 s2 =
	let rec o_help new_subs subs = function
		| [] -> List.rev (List.append subs new_subs)
		| (x,nx)::xs -> o_help ((x, substitute subs nx)::new_subs) subs xs in
	o_help [] s1 s2;;

(* Vindt alle vrije variabelen in een gegeven type t *)
let tv t =
	let rec tv_help list = function
		| Var i -> List.rev (i::list)
  	| Imp (t1,t2) -> List.concat [(tv_help [] t1);(tv_help [] t2);list]
  	| Tup (t1,t2) -> List.concat [(tv_help [] t1);(tv_help [] t2);list]
  	| Lis t -> tv_help list t
  	| t -> [] in
	remove_dups (tv_help [] t);;

let unexpected expected found = 
	sprintf "Found type '%s' where type '%s' was expected." (string_of_type found) (string_of_type expected);;

let u t1 t2 =
	let rec u_help list t = function
  	| Var a ->
  		(match t with
  		| Var a1 when (a = a1) -> Success (List.rev list)
  		| x when (not (isIn a (tv x))) -> Success (List.rev ((a,x)::list))
			| _ -> Error (unexpected (Var a) t))
  	| Imp (t1,t2) ->
			(match t with
			| Imp (s1, s2) ->
				(match u_help [] s2 t2 with
				| Success x ->
					(match u_help [] (substitute x s1) (substitute x t1) with
					| Success left -> Success (o left x)
					| Error e -> Error ("Unable to unify arguments, due to:\n" ^ e))
				| Error e -> Error ("Unable to unify result, due to:\n" ^ e))
			| Var a when (not (isIn a (tv (Imp (t1,t2))))) -> Success (List.rev ((a,Imp (t1,t2))::list))
			| _ -> Error (unexpected (Imp (t1,t2)) t))
  	| Tup (t1,t2) ->
			(match t with
			| Tup (s1, s2) ->
				(match u_help [] s2 t2 with
				| Success x ->
					(match u_help [] (substitute x s1) (substitute x t1) with
					| Success left -> Success (o left x)
					| Error e -> Error ("Unable to unify right side of tuples, due to:\n" ^ e))
				| Error e -> Error ("Unable to unify left side of tuples, due to:\n" ^ e))
			| Var a when (not (isIn a (tv (Tup (t1,t2))))) -> Success (List.rev ((a,Tup (t1,t2))::list))
			| _ -> Error (unexpected (Tup (t1,t2)) t))
  	| Lis t1 ->
			(match t with
			| Lis s1 -> u_help [] s1 t1
			| Var a when (not (isIn a (tv (Lis t1)))) -> Success (List.rev ((a,(Lis t1))::list))
			| _ -> Error (unexpected (Lis t1) t))
  	| t1 ->
			(match t with
			| Var a when (not (isIn a (tv t1))) -> Success (List.rev ((a,t1)::list))
			| t2 when (t1 = t2) -> Success (List.rev list)
			| _ -> Error (unexpected t1 t)) in
	u_help [] t1 t2;;


(* Env: (x,a,t) ? *)
let rec m env exp = function
	| var -> m_help env var exp
and m_help env var = function
	| Exp_int _ -> u Int var
	| Exp_bool _ -> u Bool var
	| Exp_char _ -> u Char var
	| Exp_infix (e1, (Op2 op), e2) when (is_op_plus op || is_op_times op) ->
		(match m env e1 Int with
		| Success x1 ->
			(match m (substitute x1 env) e2 Int with (* Wat staat er in die environment? *)
			| Success r1 ->
				(let x = o r1 x1 in
				(match u (substitute x var) Int with
				| Success r2 -> Success (o r2 x)
				| Error e -> Error ("Complete expression not an int because of:\n" ^ e)))
			| Error e -> Error ("Second part of expression not an int because of:\n" ^ e))
		| Error e -> Error ("First part of expression not an int because of:\n" ^ e))
	| _ -> Error "Unsupported expression";;

match (m Int (Exp_infix ((Exp_bool true), Op2 "+", (Exp_int (Inttoken 2)))) (Var "b")) with
| Success x -> print_subs stdout x;
| Error e -> print_string e;;