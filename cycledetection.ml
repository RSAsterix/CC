open Stack
open Type_graph

let s = create();;
let index = ref 0;;

let tarjan graph =
	let rec outerloop sccs = function
		| [] -> sccs
		| v::vs when (v.i = -1) ->
			outerloop (strongconnect sccs v) vs
		| _::vs -> outerloop sccs vs 
	and strongconnect sccs = function
		| v ->
			v.i <- !index;
			v.lowlink <- !index;
			index := !index + 1;
			push v s;
			v.onStack <- true;
			
			let rec innerloop sccs' = function
				| [] -> sccs'
				| e::es when (e.t.i = -1) ->
					(let sccs'' = strongconnect sccs' e.t in
					v.lowlink <- min v.lowlink e.t.lowlink;
					innerloop sccs'' es)
				| e::es when (e.t.onStack) ->
					v.lowlink <- min v.lowlink e.t.i;
					innerloop sccs' es
				| _::es -> innerloop sccs' es in
			
			(let sccs' = innerloop sccs (get_e_f v.id graph) in
			
			if v.lowlink = v.i then
				let rec repeat scc = function
					| w when (w = v) ->
						w.onStack <- false;
						(w::scc)
					| w ->
						w.onStack <- false;
						repeat (w::scc) (pop s) in
				(repeat [] (pop s))::sccs' 
			else
				sccs')
		in
	List.rev (outerloop [] graph.v);;