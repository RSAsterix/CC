type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

module SS = Set.Make(String);;

module RW = Set.Make(
	struct
		type t = string * types
		let compare x y = compare (fst x) (fst y)
	end)

type env_var = {
	id : string;
	mutable t : types;}

module Env_var = Set.Make(
	struct
		type t = env_var
		let compare x y = compare x.id y.id
	end)

type env_fun = {
	id : string;
	mutable bound : SS.t;
	mutable t : types;
	mutable locals : Env_var.t;}

module Env_fun = Set.Make(
  struct
    type t = env_fun
    let compare x y = compare x.id y.id
  end);;

type environment = Env_var.t * Env_fun.t;;