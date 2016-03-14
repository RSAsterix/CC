open Printf

type types = 
	| Var of string
	| Imp of types * types
	| Tup of types * types
	| Lis of types
	| Int | Bool | Char;;

let rec remove_dups lst = 
	match lst with
	| [] -> []
	| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));;

let rec string_of_type = function
	| Var s -> sprintf "%s" s
	| Imp (t1,t2) -> sprintf "%s -> %s" (string_of_type t1) (string_of_type t2)
	| Tup (t1,t2) -> sprintf "(%s,%s)" (string_of_type t1) (string_of_type t2)
	| Lis t -> sprintf "[%s]" (string_of_type t)
	| Int -> sprintf "int"
	| Bool -> sprintf "bool"
	| Char -> sprintf "char";;
 

let print_subs out subs =
	let rec subs_print_help out = function
	| [] -> ()
	| [(x,nx)] -> fprintf out "%s |-> %s" x (string_of_type nx)
	| el::xs -> fprintf out "%a, %a" subs_print_help [el] subs_print_help xs in
	fprintf out "[%a]" subs_print_help subs;;

let isIn el lst = List.exists (fun x -> x = el) lst;;  