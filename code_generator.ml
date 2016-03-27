open String
open Types

(* TODO: *)
(* it should be possible to use functions and global variables before they are defined *)
(* onze tokenizer moet comments wegmieteren *)
(* ids hebben ook hun type nodig *)

(* besluiten *)
(* "<type> id = exp" maakt een id *)
(* "var id = exp" verandert een id *) 
(* lists zijn single linkedlists, oftewel tuples van (waarde, pointer naar volgende plek) *)
(* Er is een ongebruikte plek in de heap. Als een list hier naar point, is hij empty *)

(* open Set   *)


(* module Id =                                  *)
(*      struct                                  *)
(*        type t = int * string                 *)
(*        let compare (x0,y0) (x1,y1) =         *)
(*          match Pervasives.compare y0 y1 with *)
(*            | 0 -> Pervasives.compare x0 x1   *)
(*            | c -> c                          *)
(*      end                                     *)

(* module Ids = Set.Make(Id)                    *)

(* definities: *)
(* A needs B: decl bevat het id die in B gedefinieerd wordt *)
(* B owns A: als A needs B *)

(* needless decls moeten bovenaan *)
(* ownless decls moeten onderaan *)

(* var en functie declaraties moeten in volgorde zodat als A needs B, dan staat A onder B. *)

(* een functie heeft fargs, vardecls en stmts *)
(* alle fargs zijn lokaal *)
(* alle nieuwe vardecls zijn ook lokaal *)
(* alle stmts zijn needs *)

(* Hoe handelen we global vars? *)
(* Wij hebben een lijst van vars, zowel basic als groter *)
(* Het grootste probleem is zorgen dat we de volgende waarde in een lijst vinden *)

(* Ga over de vardeclarations. *)
(* Als een basicvar gedeclareerd wordt, reserveer 1 plek *)
(* Als een lijst of tuple gedeclareerd wordt, reserveer 2 plekken *)
(* Skip idtypes voor nu *)

let get_ids ids = function
	| Vardecl (_,id,_)::decllist -> get_ids (0,id)::ids decllist
	| Fundecl (id,fargs,_,_,_)::decllist -> get_ids (length fargs,id)::ids decllist
	| [] -> ids

type info = (* alle side information nodig naast de structure en de code *)
	{
		idtypes: (string * typetoken) list
	}

(* exp_infix voorbeeld *)
(* 2 + 3 *)
(*LDC	2
	LDC	3
	ADD *)

let rec exp_gen info exp =
	match exp with
	| Exp_field fieldexp -> field_gen fieldexp
	| Exp_infix (exp1,op,exp2) -> 
		match exp_gen info exp1 with
		| Success (info,code1) -> 
			match exp_gen info exp2 with
			| Success (info,code2) ->
				| info, append (code1) (append (code2) (op2_gen op))

let vardecl_gen info code decl = 
	match decl with
	| Vardecl (Some (typetoken),id,exp) ->
		match exp_gen info exp with
		match typetoken with
		| Basictype _ -> 

let emptylistcode = "
ldc 0 \n
sth \n
str EMPTYLIST \n
"

let startcode ids code nr = function
	| Vardecl(Some(Basictype b),id,_)::decllist -> startcode ((b,id,nr)::ids) ("ldc 0 \nsth \n" ^ code) nr+1 decllist
	| Vardecl(Some(Type_tuple t),id,_)::decllist
	| Vardecl(Some(Type_list t),id,_)::decllist -> startcode ((t,id,nr)::ids) ("ldc 0 \nsth \nldc 0 \nsth \n" ^ code) nr+2 decllist
	| [] -> (ids,emptylist ^ code)
	


let spl_gen ids code info = function
  	| [] -> code
  	| Vardecl (Some (Basictype,id,exp) -> vardecl_gen code info decl
  	| Decl_fun decl -> fundecl_gen code info decl
