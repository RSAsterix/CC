type types = 
	| Var of string 				(* Var "a" *)
	| Imp of types * types 	(* Imp(a,b) = a -> b *)
	| Tup of types * types 	(* Tup(a,b) = (a,b) *)
	| Lis of types 					(* Lis a = [a] *)
	| Enum of (string * types option) list
	| Int | Bool | Char | Void;;

exception Already_known of string;;
exception Not_in_env of string;;

module SS = Set.Make(String);;

type env_type = {
	id : string;
	t : types;
	};;

module TypeSet = 
	Set.Make(
		struct
			type t = env_type
			let compare x y = compare x.id y.id
		end
		);;

module Env_type =
	struct
		include TypeSet
		let stub x : env_type = 
			{id = x; t = Void} 
		let find_safe x set =
			try find x set
			with
			| Not_found -> raise (Not_in_env x.id)
		let add_safe x set =
			try
				let _ = find x set in
				raise (Already_known x.id)
			with
			| Not_found -> add x set
		let update x set =
			let y = find_safe x set in
  		let set' = remove y set in
  		add x set'
		let union_safe set1 set2 =
			fold (fun el beginset -> add_safe el beginset) set1 set2
	end
	;;

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
		let stub x : env_var = 
			{id = x; t = Void}
		let find_safe x set =
			try find x set
			with
			| Not_found -> raise (Not_in_env x.id)
		let add_safe x set =
			try
				let _ = find x set in
				raise (Already_known x.id)
			with
			| Not_found -> add x set
		let update x set =
			let y = find_safe x set in
  		let set' = remove y set in
  		add x set'
		let add_locals x set =
			fold (fun el beginset ->
				try
					update el beginset
				with
				| Not_in_env e -> add_safe el beginset) x set
		let exclude x set =
			let y = find_safe {id = x; t = Void} set in
			remove y set
		let union_safe set1 set2 =
			fold (fun el beginset -> add_safe el beginset) set1 set2
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
		let stub x =
			{id = x; bound = SS.empty; t = Void; locals = Env_var.empty}
		let find_safe x set =
			try find x set
			with
			| Not_found -> raise (Not_in_env x.id) 
		let add_safe x set =
			try
				let _ = find x set in
				raise (Already_known x.id)
			with
			| Not_found -> add x set
		let update x set =
  		let y = find_safe x set in
  		let set' = remove y set in
  		add x set'
		let union_safe set1 set2 =
			fold (fun el beginset -> add_safe el beginset) set1 set2
	end;;

type environment = {
	types : Env_type.t;
	vars : Env_var.t;
	funs : Env_fun.t;};;

module Env =
	struct 
		type t = environment
		let empty = {
			types = Env_type.empty;
			vars = Env_var.empty;
			funs = Env_fun.empty;}
		let union x y = {
			types = Env_type.union x.types y.types;
			vars = Env_var.union x.vars y.vars;
			funs = Env_fun.union x.funs y.funs;}
		let diff x y = {
			types = Env_type.diff x.types y.types;
			vars = Env_var.diff x.vars y.vars;
			funs = Env_fun.diff x.funs y.funs;}
		let elements env =
			Env_type.elements env.types,
			Env_var.elements env.vars,
			Env_fun.elements env.funs
		
		let find_type x env =
			Env_type.find_safe (Env_type.stub x) env.types
		let add_type x env = {
			env with types = 
				Env_type.add_safe x env.types}
		let update_var x env = {
			env with types =
				Env_type.update x env.types}
		
		let find_var x env =
			Env_var.find_safe (Env_var.stub x) env.vars
		let add_var x env = {
			env with vars = 
				Env_var.add_safe x env.vars}
		let update_var x env = {
			env with vars =
				Env_var.update x env.vars}
		
		let find_fun x env =
			Env_fun.find_safe (Env_fun.stub x) env.funs
		let add_fun x env = {
			env with funs =
				Env_fun.add_safe x env.funs}
		let update_fun x env = {
			env with funs =
				Env_fun.update x env.funs}
		
		let add_locals locals env = {
			env with vars =
				Env_var.add_locals locals env.vars}
		let exclude x env = {
			env with vars =
				Env_var.exclude x env.vars}
		let exists_cons x env =
			try
				let _ = find_type x env in
				true
			with
			| Not_in_env _ -> false
	end;;
	
module RW = Set.Make(
	struct
		type t = string * types
		let compare x y = compare (fst x) (fst y)
	end)