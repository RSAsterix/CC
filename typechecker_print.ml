open Printf
open Typechecker_types
open Format

let rec string_of_type = function
	| Var s -> sprintf "%s" s
	| Imp (t1,t2) -> sprintf "%s -> %s" (string_of_type t1) (string_of_type t2)
	| Tup (t1,t2) -> sprintf "(%s,%s)" (string_of_type t1) (string_of_type t2)
	| Lis t -> sprintf "[%s]" (string_of_type t)
	| Enum enum -> "custom enum"
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

(* let print_env env =                                                            *)
(* 	let rec subs_print_help = function                                           *)
(* 	| [] -> ""                                                                   *)
(* 	| [el] ->                                                                    *)
(* 		(match el.bound with                                                       *)
(* 		| [] -> sprintf "%s |-> %s" el.id (string_of_type el.t)                    *)
(* 		| x -> sprintf "%s |-> %s %s" el.id (print_list x) (string_of_type el.t))  *)
(* 	| el::xs -> sprintf "%s\n %s" (subs_print_help [el]) (subs_print_help xs) in *)
(* 	sprintf "[%s\n]" (subs_print_help !env);;                                    *)

let prettyprint_env env =
	(* id :: type *)
	let print_variable (el : Env_var.elt) =
		sprintf "'%s' :: '%s'" el.id (string_of_type el.t) in
	
	let print_forall (list : SS.elt list) =
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
	let print_locals (list : Env_var.elt list) =
		(let rec helper = function
  		| [] -> ""
  		| [l] -> sprintf "@;<0 2>%s" (print_variable l)
  		| l::ls -> sprintf "@;<0 2>%s%s" (print_variable l) (helper ls) in
		match list with
		| [] -> ""
		| ls -> sprintf "Locals:%s@," (helper ls)) in
	
	let print_function el =
		sprintf "%s :: %s%s@;<0 2>@[<v 0>%s@]" el.id (print_forall (SS.elements el.bound)) (string_of_type el.t) (print_locals (Env_var.elements el.locals)) in
	
	let varstring = ref "" in
	let vars v = Env_var.iter (fun el -> varstring := (sprintf "@[<v 0>%s@]@." (print_variable el)) ^ !varstring) v in
	
	let funstring = ref "" in
	let funs f = Env_fun.iter (fun el -> funstring := (sprintf "@[<v 0>%s@]@." (print_function el)) ^ !funstring) f in
	
	vars env.vars;
	funs env.funs;
	
	sprintf "%s\n%s" !varstring !funstring;;

let unexpected expected found = 
	sprintf "Found type '%s' where type '%s' was expected." (string_of_type found) (string_of_type expected);;