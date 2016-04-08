open Printf
open Types

type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

type env_val = {
	id : string;
	mutable forall : string list;
	mutable t : types
	}

type environment = {
	mutable e : env_val list;
	}

let rec remove_dups lst = 
	match lst with
	| [] -> []
	| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));;

let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1
let rec find_dups l1 l2 = List.filter (fun x -> List.exists (fun y -> fst y = x) l2) (List.map (fun x -> fst x) l1);;
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
	| a::rest -> sprintf "%s, %s" a (print_list rest)
	sprintf "[%s] " (help list);;

let print_env env =
	let rec subs_print_help = function
	| [] -> ""
	| [el] -> sprintf "%s |-> %s%s" el.id (print_list el.forall) el.t
	| el::xs -> sprintf "%s\n %s" (subs_print_help [el]) (subs_print_help xs) in
	fprintf out "[%a\n]" subs_print_help env.e;;

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
	| Var i -> rewrite subs (Var i)
	| Imp (t1,t2) -> Imp (substitute subs t1, substitute subs t2)
	| Tup (t1,t2) -> Tup (substitute subs t1, substitute subs t2)
	| Lis t -> Lis (substitute subs t)
	| t -> t;;

let substitute_list subs env =
	let rec sub_list_help subs = function
		| [] -> ();
		| el::xs -> el.t <- (substitute subs el.t); sub_list_help subs xs in
	sub_list_help subs env.e;;
	
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

let tv_list env =
	let rec tv_help free bound = function
		| [] -> List.rev free
		| el::rest ->
			(let newbound = List.append el.forall (el.id::bound) in
			tv_help (diff (tv el.t) newbound) newbound rest) in
	tv_help [] [] env.e;;

let unexpected expected found = 
	sprintf "Found type '%s' where type '%s' was expected." (string_of_type found) (string_of_type expected);;

let u t1 t2 =
	let rec u_help list t = function
  	| Var a ->
  		(match t with
  		| Var a1 when (a = a1) -> Success (List.rev list)
  		| x when (not (List.mem a (tv x))) -> Success (List.rev ((a,x)::list))
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
			| Var a when (not (List.mem a (tv (Imp (t1,t2))))) -> Success (List.rev ((a,Imp (t1,t2))::list))
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
			| Var a when (not (List.mem a (tv (Tup (t1,t2))))) -> Success (List.rev ((a,Tup (t1,t2))::list))
			| _ -> Error (unexpected (Tup (t1,t2)) t))
  	| Lis t1 ->
			(match t with
			| Lis s1 -> u_help [] s1 t1
			| Var a when (not (List.mem a (tv (Lis t1)))) -> Success (List.rev ((a,(Lis t1))::list))
			| _ -> Error (unexpected (Lis t1) t))
  	| t1 ->
			(match t with
			| Var a when (not (List.mem a (tv t1))) -> Success (List.rev ((a,t1)::list))
			| t2 when (t1 = t2) -> Success (List.rev list)
			| _ -> Error (unexpected t1 t)) in
	u_help [] t1 t2;;

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
	| _::rest -> env_find x rest in
	help env.e;;

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