let index = ref 0;;
let s = ref [];;
let increase = index := !index + 1;;
let push v = s := v::!s;;
let pop = s := List.tl s;;

type vertex = {
	id : string;
	mutable i : int;
	mutable lowlink : int;
	mutable onStack : bool;}

type edge = {
	f : vertex;
	t : vertex;}

let tarjan vertices edges =
	let rec loop2 v = function
  	| [] -> ()
  	| edge::restedges when (edge.t.index = -1) -> 
  		strongconnect edges edge.t;
  		v.lowlink <- min v.lowlink, edge.t.index;
  		loop2 v restedges
  	| edge::edges when (edge.t.onStack) ->
  		v.lowlink <- min v.lowlink edge.t.index;
  		loop2 v restedges 
  	| _::restedges -> loop2 v restedges
  and strongconnect = function
  	| v ->
  		v.i <- index;
  		v.lowlink <- index;
  		increase;
  		push v;
  		v.onStack <- true;
  		loop2 v edges;
			if v.lowlink = v.index
			then 
				
  	| 
		
		
		
		 

let rec loop1 e = function
	| [] -> ()
	| v::vertices when (v.index = -1) -> strongconnect e v; loop1 e vertices
	| _::vertices -> loop1 e vertices;;

let tarjan = function
	| vertices, edges ->   