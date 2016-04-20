type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

module TV = Set.Make(String);;

type env_var = {
	id : string;
	mutable t : types;}

type env_fun = {
	id : string;
	mutable bound : string list;
	mutable t : types;
	mutable locals : env_var list;}

type env_val = 
	| Variable of env_var
	| Function of env_fun;;

module Env = Set.Make(
  struct
    type t = env_val
    let compare x y =
      match x with
      | Variable var1 ->
      	(match y with
      	| Variable var2 -> if var1.id = var2.id then 0 else if var1.id < var2.id then -1 else 1
      	| Function _ -> -1)
      | Function fun1 ->
      	(match y with
      	| Function fun2 -> if fun1.id = fun2.id then 0 else if fun1.id < fun2.id then -1 else 1
      	| Variable _ -> 1)
  end);;