open Types
open Format
open Typechecker_types
open Typechecker_print

(* nieuwe variabele genereren:*)
(* roep eerst fresh(); aan*)
(* gebruik vervolgens "Var !v" voor een verse variabele*)
(* dit gaat goed, omdat een normale Var nooit met een cijfer kan beginnen*)
let c = ref 0;;
let v = ref "";;
let fresh = function
	| _ ->
		c := !c + 1;
		v := (string_of_int !c) ^ "f";;

(* herschrijfregel uit subs gebruiken   *)
(* subs = [x1 |-> nx1; x2 |-> nx2; ...] *) 
let rec rewrite (subs : RW.t) i =
	try
		snd (RW.find (i,Void) subs)
	with
	| _ -> Var i;;

(* substitutieregels toepassen *)
let rec substitute subs = function
	| Var i -> rewrite subs i
	| Imp (t1,t2) -> Imp (substitute subs t1, substitute subs t2)
	| Tup (t1,t2) -> Tup (substitute subs t1, substitute subs t2)
	| Lis t -> Lis (substitute subs t)
	| t -> t;;

let substitute_vars subs varenv =
	Env_var.fold (
		(fun x ev -> Env_var.add 
		{x with t = substitute subs x.t} ev))
		varenv Env_var.empty;;

let substitute_funs subs funenv =
	Env_fun.fold
		(fun x ef -> Env_fun.add 
		{x with t = substitute subs x.t; locals = substitute_vars subs x.locals} ef)
		funenv Env_fun.empty;; 

let substitute_env subs env =
	let newvars = substitute_vars subs (fst env) in
	let newfuns = substitute_funs subs (snd env) in
	(newvars, newfuns);;
	
(* Infix versie van o, vervangt alle substituties in s2 *)
(* volgens de regels in s1 *)
let o rw1 rw2 =
	let new_rw1 = RW.fold (fun x rw -> RW.add (fst x, substitute rw2 (snd x)) rw) rw1 RW.empty in
	RW.union new_rw1 rw2;;

(* Vindt alle vrije variabelen in een gegeven type t *)
let tv t =
	let rec tv_help (free : SS.t) = function
		| Var i -> SS.add i free
  	| Imp (t1,t2) -> SS.union (tv_help free t1) (tv_help free t2)
  	| Tup (t1,t2) -> SS.union (tv_help free t1) (tv_help free t2)
  	| Lis t -> tv_help free t
  	| t -> free in
	tv_help SS.empty t;;

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
	| (Var a, Var b) when a = b -> Success RW.empty
	| (Var a, t) when not (SS.mem a (tv t)) -> Success (RW.singleton (a,t))
	| (t, Var a) when not (SS.mem a (tv t)) -> Success (RW.singleton (a,t))
	| (Imp (s1,s2), Imp (t1,t2)) ->
		(match u (s2, t2) with
		| Error e -> Error ("Could not match second parts of implications:\n" ^ e)
		| Success x ->
			match u (substitute x s1, substitute x t1) with
			| Error e -> Error ("Could not match first parts of implications:\n" ^ e)
			| Success res -> Success (o res x))
	| (Tup (s1,s2), Tup (t1,t2)) -> u (Imp (s1,s2), Imp (t1,t2))
	| (Lis s, Lis t) -> u (s,t)
	| (Int, Int) -> Success RW.empty
	| (Bool, Bool) -> Success RW.empty
	| (Char, Char) -> Success RW.empty
	| (Void, Void) -> Success RW.empty
	| (x,y) -> Error (unexpected x y);;

(* Converts operator of an expression (x op y) like this: *)
(* (type x),(type y),(type (x op y)) *) 
let op2_to_subs = function
	| Listop -> fresh(); (Var !v), (Lis (Var !v)), (Lis (Var !v))
	| Logop _ -> Bool, Bool, Bool
	| Eqop _ -> fresh(); (Var !v), (Var !v), Bool
	| Compop _ -> Int, Int, Bool
	| Weakop _ -> Int, Int, Int
	| Strongop _ -> Int, Int, Int;;

let op1_to_subs = function
	| Not -> Bool
	| Neg -> Int;;

let env_var_find x env = 
	Env_var.find {id = x; t = Void} (fst env);;

let env_fun_find x env =
	Env_fun.find {id = x; bound = SS.empty; t = Void; locals = Env_var.empty} (snd env);;

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

let rec dups = function
| [] -> false
| x::xs when List.mem x xs -> true
| _::xs -> dups xs;;