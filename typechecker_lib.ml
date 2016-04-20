open Types
open Format
open Typechecker_types
open Typechecker_print

(* nieuwe variabele genereren:*)
(* roep eerst fresh; aan*)
(* gebruik vervolgens "Var !v" voor een verse variabele*)
(* dit gaat goed, omdat een normale Var nooit met een cijfer kan beginnen*)
let c = ref 0;;
let v = ref "";;
let fresh =
		c := !c + 1;
		v := (string_of_int !c) ^ "f";;

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

let substitute_env subs (env : environment) =
	let f x = x.t <- substitute subs x.t in
	Env_var.iter f (fst env);
	Env_fun.iter f (snd env);;
	
(* Infix versie van o, vervangt alle substituties in s2 *)
(* volgens de regels in s1 *)
let o s1 s2 =
	let rec o_help new_subs subs = function
		| [] -> List.append subs new_subs
		| (x,nx)::xs -> o_help ((x, substitute subs nx)::new_subs) subs xs in
	o_help [] s1 s2;;

(* Vindt alle vrije variabelen in een gegeven type t *)
let tv t =
	let rec tv_help (free : SS.t) = function
		| Var i -> TV.add i free
  	| Imp (t1,t2) -> TV.union (tv_help free t1) (tv_help free t2)
  	| Tup (t1,t2) -> TV.union (tv_help free t1) (tv_help free t2)
  	| Lis t -> tv_help free t
  	| t -> free in
	tv_help TV.empty t;;

let tv_env_var (env_var : Env_var.t) =
	Env_var.fold (fun x beginfree -> SS.union beginfree (tv x.t)) env_var (SS.empty);;

let tv_env_fun (env_fun : Env_fun.t) =
	Env_fun.fold (fun x beginfree ->
		let part1 = SS.diff (SS.union beginfree (tv x.t)) x.bound in
		let part2 = SS.diff (tv_env_var x.locals) x.bound in
		SS.union part1 part2) env_fun (SS.empty);;

let tv_env (env : environment) = 
	SS.union (tv_env_var (fst env)) (tv_env_fun (snd env));;

let rec u = function
	| (Var a, Var b) when a = b -> Success []
	| (Var a, t) when not (SS.mem a (tv t)) -> Success [a,t]
	| (t, Var a) when not (SS.mem a (tv t)) -> Success [a,t]
	| (Imp (s1,s2), Imp (t1,t2)) ->
		(match u (s2, t2) with
		| Error e -> Error ("Could not match second parts of implications:\n" ^ e)
		| Success x ->
			(match u (substitute x s1, substitute x t1) with
			| Error e -> Error ("Could not match first parts of implications:\n" ^ e)
			| Success res -> Success (o res x)))
	| (Tup (s1,s2), Tup (t1,t2)) -> u (Imp (s1,s2), Imp (t1,t2))
	| (Lis s, Lis t) -> u (s,t)
	| (Int, Int) -> Success []
	| (Bool, Bool) -> Success []
	| (Char, Char) -> Success []
	| (Void, Void) -> Success []
	| (x,y) -> Error (unexpected x y);;

(* Converts operator of an expression (x op y) like this: *)
(* (type x),(type y),(type (x op y)) *) 
let op2_to_subs = function
	| Listop -> fresh; (Var !v), (Lis (Var !v)), (Lis (Var !v))
	| Logop _ -> Bool, Bool, Bool
	| Eqop _ -> fresh; (Var !v), (Var !v), Bool
	| Compop _ -> Int, Int, Bool
	| Weakop _ -> Int, Int, Int
	| Strongop _ -> Int, Int, Int;;

let op1_to_subs = function
	| Not -> Bool
	| Neg -> Int;;

let env_var_find x (env : Env_var.t) = 
	Env_var.find {id = x; t = Void} env;;

let env_fun_find x (env : Env_fun.t) =
	Env_fun.find {id = x; bound = SS.empty; t = Void; locals = Env_var.empty} env;;

let rec convert_typetoken = function
	| Type_int -> Int
	| Type_bool -> Bool
	| Type_char -> Char
	| Type_tuple (t1,t2) -> Tup (convert_typetoken t1, convert_typetoken t2)
	| Type_list t -> Lis (convert_typetoken t)
	| Type_id id -> Var id;;  

let convert_rettype = function
	| Type_void -> Void
	| Rettype t -> convert_typetoken t;;

let rec make_type = function
	| ([],rettype) -> convert_rettype rettype
	| (a::rest,rettype) -> Imp (convert_typetoken a, make_type (rest,rettype));;