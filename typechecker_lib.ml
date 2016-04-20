open Types
open Format
open Typechecker_types
open Typechecker_print

(* let test = function *)
(* 	| None -> []      *)
(* 	| Some l -> l;;   *)

(* let test_decl = function        *)
(* 	| Some (Fundecl _) -> Some [] *)
(* 	| _ -> None;;                 *)

(* let environment : env_val list ref = ref [];; *)

(* let rec remove_dups lst =                                      *)
(* 	match lst with                                               *)
(* 	| [] -> []                                                   *)
(* 	| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));; *)

(* let rec add_nodups l1 = function                                                                                    *)
(* 	| [] -> l1                                                                                                        *)
(* 	| el::l2 when (List.mem el l1) -> add_nodups l1 l2                                                                *)
(* 	| el::l2 -> add_nodups (el::l1) l2;;                                                                              *)
(* let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1                                                      *)
(* let rec find_dups l1 l2 = List.filter (fun x -> List.exists (fun y -> y.id = x) l2) (List.map (fun x -> x.id) l1);; *)
(* let rec substract l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1;;                                           *)
(* let first list =                                                                                                    *)
(* 	let rec f_help result = function                                                                                  *)
(* 		| [] -> []                                                                                                      *)
(* 		| [_] -> List.rev result                                                                                        *)
(* 		| a::rest -> f_help (a::result) rest in                                                                         *)
(* 	f_help [] list;;                                                                                                  *)
(* let rec last = function                                                                                             *)
(* 	[] -> ()                                                                                                          *)
(* 	| [a] -> a                                                                                                        *)
(* 	| _::rest -> last rest;;                                                                                          *)


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

let substitute_list subs (env : Env.t) =
	Env.iter (fun x -> match x with
	| Variable xv -> xv.t <- substitute subs xv.t
	| Function xf -> xf.t <- substitute subs xf.t) env;;
	
(* Infix versie van o, vervangt alle substituties in s2 *)
(* volgens de regels in s1 *)
let o s1 s2 =
	let rec o_help new_subs subs = function
		| [] -> List.append subs new_subs
		| (x,nx)::xs -> o_help ((x, substitute subs nx)::new_subs) subs xs in
	o_help [] s1 s2;;

(* Vindt alle vrije variabelen in een gegeven type t *)
let tv t =
	let rec tv_help (free : TV.t) = function
		| Var i -> TV.add i free
  	| Imp (t1,t2) -> TV.union (tv_help free t1) (tv_help free t2)
  	| Tup (t1,t2) -> TV.union (tv_help free t1) (tv_help free t2)
  	| Lis t -> tv_help free t
  	| t -> free in
	tv_help TV.empty t;;

let tv_list (env : Env.t) =
  	Env.fold (fun x beginfree -> match x with
  	| Variable xv -> TV.union beginfree (tv xv.t)  
  	| Function xf -> TV.diff (TV.union beginfree (tv xf.t)) (TV.of_list xf.bound)) env;;

let rec u = function
	| (Var a, Var b) when a = b -> Success []
	| (Var a, t) when not (TV.mem a (tv t)) -> Success [a,t]
	| (t, Var a) when not (TV.mem a (tv t)) -> Success [a,t]
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

let env_find x (env : Env.t) = 
	Env.find x env;;

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