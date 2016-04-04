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

let add_v s d vertices =
	if (List.exists (fun x -> s = x.id) vertices)
	then 
		(match d with
		| None -> vertices
		| _ -> 
			(get_v s vertices).spl_decl <- d;
			(let rec replace = function
				| [] -> ()
				| e::es -> e.t.spl_decl <- d in 
			replace (to_v [] (get_v s vertices));
			vertices))
	else 
		{id = s; i = -1; lowlink = -1; onStack = false; spl_decl = d}::vertices;;

let rec get_v s vertices = try (List.find (fun x -> x.id = s) vertices) with
| _ -> get_v s (add_v s None vertices);;

let rec from res vertex = function
	| [] -> res
	| edge::edges when (edge.f.id = vertex.id) -> from (edge::res) vertex edges
	| _::edges -> from res vertex edges;;

let rec to_v res vertex = function
	| [] -> res
	| edge::edges when (edge.t.id = vertex.id) -> to_v (edge::res) vertex edges
	| _::edges -> to_v res vertex edges;;

let add_e (vertices, edges) src dest = 
	{f = (get_v src vertices); t = (get_v dest vertices)}::edges;; 