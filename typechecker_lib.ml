type types = 
	| Var of int
	| Imp of types * types
	| Tup of types * types
	| Lis of types
	| Int | Bool | Char;;

let rec print_type out = function
	| Var i -> fprintf out "%i" i
	| Imp (t1,t2) -> fprintf out "%a -> %a" printer t1 printer t2
	| Tup (t1,t2) -> fprintf out "(%a,%a)" printer t1 printer t2
	| Lis t -> fprintf out "[%a]" printer t
	| Int -> fprintf out "int"
	| Bool -> fprintf out "bool"
	| Char -> fprintf out "char";;