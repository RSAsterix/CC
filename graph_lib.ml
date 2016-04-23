open Types

type vertex = {
	id : string;
	mutable i : int;
	mutable lowlink : int;
	mutable onStack : bool;
	spl_decl : decl;}

type edge = {
	f : vertex;
	t : vertex;}

type graph = {
	mutable v : vertex list;
	mutable e : edge list;}

let get_v s graph =
	List.find (fun x -> x.id = s) graph.v

let get_e_f s graph =
	List.find_all (fun x -> x.f.id = s) graph.e;;

let get_e_t s graph =
	List.find_all (fun x -> x.t.id = s) graph.e;;

let add_v s d graph =
	graph.v <- {id = s; i = -1; lowlink = -1; onStack = false; spl_decl = d}::graph.v;;

let add_e src dest graph =
	try
		let v_f = get_v src graph in
		(try
			let v_t = get_v dest graph in
			graph.e <- {f = v_f; t = v_t}::graph.e
		with
		| Not_found -> raise (Invalid_argument dest))
	with
	| Not_found -> raise (Invalid_argument src);;
	
	