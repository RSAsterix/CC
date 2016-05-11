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
	mutable locals : Env_var.t;}

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
		let update_fun f env =
			fst env,
			if Env_fun.mem f (snd env)
			then
    		(Env_fun.fold (fun x beginset ->
    			if (f.id = x.id)
    			then Env_fun.add f beginset
    			else Env_fun.add x beginset)
    		(snd env) Env_fun.empty)
			else
				Env_fun.add f (snd env)
		let update_var (v : env_var) env =
			if Env_var.mem v (fst env)
			then
  			(Env_var.fold (fun x beginset ->
  				if (v.id = x.id)
  				then Env_var.add v beginset
  				else Env_var.add x beginset)
  			(fst env) Env_var.empty), snd env
			else
				Env_var.add v (fst env), snd env
		let empty =
			Env_var.empty, Env_fun.empty
		let diff x y =
			Env_var.diff (fst x) (fst y), Env_fun.diff (snd x) (snd y)
		let add_locals x env =
			Env_var.fold (fun el beginenv -> update_var el beginenv) x env
		let list_vars env =
			(Env_var.fold (fun x list -> List.append list [x.id, x.t]) (fst env) [])
		let list_funs env =
			(Env_fun.fold (fun x list -> List.append list [x.id, x.t, list_vars (x.locals,Env_fun.empty)]) (snd env) [])
		let elements env =
			list_vars env, list_funs env			
	end;;
	
module RW = Set.Make(
	struct
		type t = string * types
		let compare x y = compare (fst x) (fst y)
	end)