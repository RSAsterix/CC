open Printf
open Graph_lib

let print_list l =
	let rec helper = function
  	| [] -> ""
  	| [v] -> v
		| v::vs -> v ^ ", " ^ (helper vs) in
	sprintf "[%s]" (helper l);;

let print_nodes (l : vertex list) =
	print_list (List.map (fun x -> x.id) (l : vertex list));;

let print_edges l =
	print_list (List.map (fun x -> x.f.id ^ " -> " ^ x.t.id) l);;

let string_of_graph (graph : graph) =
	sprintf "Nodes: %s\nEdges: %s" (print_nodes graph.v) (print_edges graph.e);;