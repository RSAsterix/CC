open Typechecker_lib
open Types

(* nieuwe variabele genereren *)
let c = ref 0;;
let fresh = function
	| _ -> c := !c + 1;;

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
		| [] -> List.rev (List.append new_subs subs)
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

let rec u = function
	| tuple -> u_help [] tuple 
and u_help list = function
	| (Var a1, Var a2) when (a1 = a2) -> List.rev list
	| (Var a, t) when (not (isIn a (tv t))) -> List.rev ((a,t)::list)
	| (t, Var a) when (not (isIn a (tv t))) -> List.rev ((a,t)::list)
	| (Imp (s1, s2), Imp (t1, t2)) -> 
		(let x = u (s2, t2) in
		(let u1 = u (substitute x s1, substitute x t1) in
		(let result = o u1 x in
		List.append result list)))
	| (Tup (s1, s2), Tup (t1, t2)) ->
		(let x = u (s2, t2) in
		(let u1 = u (substitute x s1, substitute x t1) in
		(let result = o u1 x in
		List.append result list)))
	| (Lis s, Lis t) ->
		(let result = u (s, t) in
		List.append result list)
	| (Int, Int) -> List.rev list
	| (Bool, Bool) -> List.rev list
	| (Char, Char) -> List.rev list
	| tuple -> [];; (* fail? *)