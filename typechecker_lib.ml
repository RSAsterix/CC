open Printf
open Types
open Format

type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

type env_val = {
	id : string;
	mutable forall : string list;
	mutable t : types;
	mutable locals : env_val list option;
	}

let test = function
	| None -> []
	| Some l -> l;;

let test_decl = function
	| Some (Fundecl _) -> Some []
	| _ -> None;;

let environment : env_val list ref = ref [];;

let rec remove_dups lst = 
	match lst with
	| [] -> []
	| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));;

let rec add_nodups l1 = function 
	| [] -> l1
	| el::l2 when (List.mem el l1) -> add_nodups l1 l2
	| el::l2 -> add_nodups (el::l1) l2;; 
let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1
let rec find_dups l1 l2 = List.filter (fun x -> List.exists (fun y -> y.id = x) l2) (List.map (fun x -> x.id) l1);;
let rec substract l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1;;
let first list =
	let rec f_help result = function
		| [] -> []
		| [_] -> List.rev result
		| a::rest -> f_help (a::result) rest in
	f_help [] list;;
let rec last = function
	[] -> ()
	| [a] -> a
	| _::rest -> last rest;;

let rec string_of_type = function
	| Var s -> sprintf "%s" s
	| Imp (t1,t2) -> sprintf "%s -> %s" (string_of_type t1) (string_of_type t2)
	| Tup (t1,t2) -> sprintf "(%s,%s)" (string_of_type t1) (string_of_type t2)
	| Lis t -> sprintf "[%s]" (string_of_type t)
	| Int -> sprintf "Int"
	| Bool -> sprintf "Bool"
	| Char -> sprintf "Char"
	| Void -> sprintf "Void";;

let print_subs out subs =
	let rec subs_print_help out = function
	| [] -> ()
	| [(x,nx)] -> fprintf out "%s |-> %s" x (string_of_type nx)
	| el::xs -> fprintf out "%a\n %a" subs_print_help [el] subs_print_help xs in
	fprintf out "[%a\n]" subs_print_help subs;;

let print_list list =
	let rec help = function
	| [] -> ""
	| [a] -> sprintf "%s" a
	| a::rest -> sprintf "%s, %s" a (help rest) in
	sprintf "forall (%s)," (help list);;

let print_env env =
	let rec subs_print_help = function
	| [] -> ""
	| [el] ->
		(match el.forall with
		| [] -> sprintf "%s |-> %s" el.id (string_of_type el.t)
		| x -> sprintf "%s |-> %s %s" el.id (print_list x) (string_of_type el.t))
	| el::xs -> sprintf "%s\n %s" (subs_print_help [el]) (subs_print_help xs) in
	sprintf "[%s\n]" (subs_print_help !env);;

(* nieuwe variabele genereren:*)
(* roep eerst fresh(); aan*)
(* gebruik vervolgens "Var !v" voor een verse variabele*)
(* dit gaat goed, omdat een normale Var nooit met een cijfer kan beginnen*)
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

let substitute_list subs env =
	let rec sub_list_help subs = function
		| [] -> ();
		| el::xs -> el.t <- (substitute subs el.t); sub_list_help subs xs in
	sub_list_help subs !env;
	env;;
	
(* Infix versie van o, vervangt alle substituties in s2 *)
(* volgens de regels in s1 *)
let o s1 s2 =
	let rec o_help new_subs subs = function
		| [] -> List.append subs new_subs
		| (x,nx)::xs -> o_help ((x, substitute subs nx)::new_subs) subs xs in
	o_help [] s1 s2;;

(* Vindt alle vrije variabelen in een gegeven type t *)
let tv t =
	let rec tv_help list = function
		| Var i -> i::list
  	| Imp (t1,t2) -> List.concat [(tv_help [] t1);(tv_help [] t2);list]
  	| Tup (t1,t2) -> List.concat [(tv_help [] t1);(tv_help [] t2);list]
  	| Lis t -> tv_help list t
  	| t -> [] in
	remove_dups (tv_help [] t);;

let tv_list env =
	let rec tv_help free bound = function
		| [] -> free
		| el::rest ->
			(let newbound = List.append el.forall (el.id::bound) in
			tv_help (diff (tv el.t) newbound) newbound rest) in
	tv_help [] [] !env;;

let unexpected expected found = 
	Error (sprintf "Found type '%s' where type '%s' was expected." (string_of_type found) (string_of_type expected));;

let rec u = function
	| (Var a, Var b) when a = b -> Success []
	| (Var a, t) when not (List.mem a (tv t)) -> Success [a,t]
	| (t, Var a) when not (List.mem a (tv t)) -> Success [a,t]
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
	| (x,y) -> unexpected x y;;

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

let env_find x env = 
	let rec help = function
	| [] -> Error ""
	| el::rest when (x = el.id) -> Success el
	| _::rest -> help rest in
	help !env;;

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

let prettyprint_env env =
	(* id :: type *)
	let print_variable el =
		sprintf "'%s' :: '%s'" el.id (string_of_type el.t) in
	
	let print_forall list =
		(let rec helper = function
			| [] -> ""
			| [f] -> sprintf "%s" f
			| f::fs -> sprintf "%s, %s" f (helper fs) in
		match list with
		| [] -> ""
		| fs -> sprintf "forall (%s), " (helper fs)) in
	
	(* []? -> ""*)
	(* l?  -> \n var*)
	(* ls? -> \n var rest *)
	let print_locals list =
		(let rec helper = function
  		| [] -> ""
  		| [l] -> sprintf "@;<0 2>%s" (print_variable l)
  		| l::ls -> sprintf "@;<0 2>%s%s" (print_variable l) (helper ls) in
		match list with
		| [] -> ""
		| ls -> sprintf "Locals:%s@," (helper ls)) in
	
	let print_function el locals =
		sprintf "%s :: %s%s@;<0 2>@[<v 0>%s@]" el.id (print_forall el.forall) (string_of_type el.t) (print_locals locals) in
	
	let rec helper = function
  	| [] -> ""
  	| el::rest ->
  		(match el.locals with
  		| None -> sprintf "@[<v 0>%s@]@.%s" (print_variable el) (helper rest)
			| Some l -> sprintf "@[<v 0>%s@]@.%s" (print_function el l) (helper rest)) in
	
	sprintf "%s" (helper !env);;