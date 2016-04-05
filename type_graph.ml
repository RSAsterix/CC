open Types

type vertex = {
	id : string;
	mutable i : int;
	mutable lowlink : int;
	mutable onStack : bool;
	mutable spl_decl : decl option}

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
	try (List.find_all (fun x -> x.f.id = s) graph.e) with
	| _ -> [];;

let get_e_t s graph =
	try (List.find_all (fun x -> x.t.id = s) graph.e) with
	| _ -> [];;

let add_v s d graph =
	match get_v s graph with
	| None -> 
		graph.v <- {id = s; i = -1; lowlink = -1; onStack = false; spl_decl = d}::graph.v;
		graph
	| Some v -> if d = None then graph else (v.spl_decl <- d; graph);;   

let rec add_e src dest graph =
	(match get_v src graph with
	| None -> add_e src dest (add_v src None graph)
	| Some src_v ->
		(match get_v dest graph with
		| None -> add_e src dest (add_v dest None graph)
		| Some dest_v ->
			graph.e <- {f = src_v; t = dest_v}::graph.e;
			graph));; 