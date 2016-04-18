open Types

type vertex = {
	id : string;
	mutable i : int;
	mutable lowlink : int;
	mutable onStack : bool;
	mutable spl_decl : decl}

type edge = {
	f : vertex;
	t : vertex;}

type graph = {
	mutable v : vertex list;
	mutable e : edge list;}

let get_v s graph =
	try Some (List.find (fun x -> x.id = s) graph.v) with
	| _ -> None;;

let get_e_f s graph =
	List.find_all (fun x -> x.f.id = s) graph.e;;

let get_e_t s graph =
	List.find_all (fun x -> x.t.id = s) graph.e;;

let add_v s d graph =
	graph.v <- {id = s; i = -1; lowlink = -1; onStack = false; spl_decl = d}::graph.v;;

let add_e src dest graph =
	match get_v src graph with
	| None -> raise (Invalid_argument src)
	| Some v_f ->
		match get_v dest graph with
		| Some v_t -> graph.e <- {f = v_f; t = v_t}::graph.e
		| None -> raise (Invalid_argument dest);;
	
	