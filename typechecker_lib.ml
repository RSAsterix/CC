open Printf

type types = 
	| Var of int
	| Imp of types * types
	| Tup of types * types
	| Lis of types
	| Int | Bool | Char;;

let rec remove_dups lst = 
	match lst with
	| [] -> []
	| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));;

let rec print_list = function
	| [] -> ()
	| e::l -> print_int e ; print_string " " ; print_list l;;

let isIn el lst = List.exists (fun x -> x = el) lst;;  

let rec print_type out = function
	| Var i -> fprintf out "%i" i
	| Imp (t1,t2) -> fprintf out "%a -> %a" print_type t1 print_type t2
	| Tup (t1,t2) -> fprintf out "(%a,%a)" print_type t1 print_type t2
	| Lis t -> fprintf out "[%a]" print_type t
	| Int -> fprintf out "int"
	| Bool -> fprintf out "bool"
	| Char -> fprintf out "char";;