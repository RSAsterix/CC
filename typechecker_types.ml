type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

module SS = Set.Make(String);;

type env_var = {
	id : string;
	t : types;}

module Env_var = Set.Make(
	struct
		type t = env_var
		let compare x y = compare x.id y.id
	end)

type env_fun = {
	id : string;
	bound : SS.t;
	t : types;
	locals : Env_var.t;}

module Env_fun = Set.Make(
  struct
    type t = env_fun
    let compare x y = compare x.id y.id
  end);;

type environment = Env_var.t * Env_fun.t;;

module Env =
	struct 
		type t = environment
		let union x y =
			Env_var.union (fst x) (fst y),
			Env_fun.union (snd x) (snd y)
		let add_var x env =
			Env_var.add x (fst env), snd env
		let add_fun x env =
			fst env, Env_fun.add x (snd env)
		let add_locals x env =
			Env_var.union x (fst env), snd env
	end;;

module RW = Set.Make(
	struct
		type t = string * types
		let compare x y = compare (fst x) (fst y)
	end)