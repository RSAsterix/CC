type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Int | Bool | Char | Void;;

exception Already_known of string;;

module SS = Set.Make(String);;

type env_var = {
	id : string;
	t : types;
	};;

module VarSet = 
	Set.Make(
  	struct
  		type t = env_var
  		let compare x y = compare x.id y.id
  	end
		);;

module Env_var =
	struct
		include VarSet
		let add_safe x set =
			try
				let _ = find x set in
				raise (Already_known x.id)
			with
			| Not_found -> add x set
		let update x set =
			let y = find x set in
			let set' = remove y set in
			add x set'
	end;;

type env_fun = {
	id : string;
	bound : SS.t;
	t : types;
	mutable locals : Env_var.t;
	};;

module FunSet = 
	Set.Make(
    struct
      type t = env_fun
      let compare x y = compare x.id y.id
    end
		);;

module Env_fun =
	struct
		include FunSet
		let add_safe x set =
			try
				let _ = find x set in
				raise (Already_known x.id)
			with
			| Not_found -> add x set
		let update x set =
			let y = find x set in
			let set' = remove y set in
			add x set'
	end;;

type environment = Env_var.t * Env_fun.t;;

module Env =
	struct 
		type t = environment
		let empty =
			Env_var.empty, Env_fun.empty
		let union x y =
			Env_var.union (fst x) (fst y),
			Env_fun.union (snd x) (snd y)
		let diff x y =
			Env_var.diff (fst x) (fst y), Env_fun.diff (snd x) (snd y)
		let elements env =
			Env_var.elements (fst env), Env_fun.elements (snd env)
		
		let find_var x env =
			Env_var.find {id = "x"; t = Void} (fst env)
		let add_var x env =
			Env_var.add_safe x (fst env), snd env
		let update_var x env =
			Env_var.update x (fst env), snd env
		
		let find_fun x env =
			Env_fun.find {id = x; bound = SS.empty; t = Void; locals = Env_var.empty} (snd env)	
		let add_fun x env =
			fst env, Env_fun.add_safe x (snd env)
		let update_fun x env =
			fst env, Env_fun.update x (snd env)
		
		let add_locals x env =
			Env_var.fold (fun el beginenv ->
				try
					update_var el beginenv
				with
				| Not_found -> add_var el beginenv) x env			
	end;;
	
module RW = Set.Make(
	struct
		type t = string * types
		let compare x y = compare (fst x) (fst y)
	end)