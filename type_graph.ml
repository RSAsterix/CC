type vertex = {
	id : string;
	mutable i : int;
	mutable lowlink : int;
	mutable onStack : bool;}

type edge = {
	f : vertex;
	t : vertex;}

