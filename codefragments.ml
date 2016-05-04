open Printf
open Types
open String

type types = 
	| Var of string
	| Imp of types * types
	| Tup of types *types
	| Lis of types
	| Int | Bool | Char | Void;;

type variabletype = id * types;;
type functiontype = {
	fid:id;
	ftype:types;
	locals:variabletype list;
	}

let empty_functiontype = {fid="henkst";ftype=Void;locals=[]}

let heapstart = 2000
let truenr =(-1)

let pointlabel l = l^": " 
let brf l = "brf "^l^" \n"
let endiflabel fid i = sprintf "endif%s%i" fid i
let bra l = "bra "^l^" \n"
let endelselabel fid i = sprintf "endelse%s%i" fid i
let startwhilelabel fid i= sprintf "startwhile%s%i" fid i
let brt l = "brt "^l^" \n"
let endwhilelabel fid i = (sprintf "endwhile%s%i" fid i)



let reservelocalcode i = sprintf "link %i \n" i

let rec reservecode i = 
"ldr HP \n"^
(sprintf "ldc %i \n" i)^ 
"add \n"^
"str HP \n"

type idstruct = {
	global: bool;
	vartype: types;
	id: string;
	index: int;
	}
	
let empty_idstruct = {global=false;vartype=Int;id="henkst";index=20}

let code_set id = 
	if id.global then
		(sprintf "ldc %i \n" heapstart)^
		(sprintf "sta %i \n" id.index)
	else
		sprintf "stl %i \n" id.index

let code_get id =
	if id.global then
		(sprintf "ldc %i \n" heapstart)^
		(sprintf "lda %i \n" id.index)
	else
		sprintf "ldl %i \n" id.index
						
let return_some_code = 
  "str RR \n"^
	"unlink \n"^
	"ret \n"

let return_none_code  =
  "unlink \n"^
	"ret \n"

(* De nieuwe headwaarde en de oude listpointer staan al op de stack *)
(* returnt de nieuwe listpointer *)
let listappendcode = "stmh 2 \n"	

let create_tuplecode ="stmh 2 \n"

let ldc x = sprintf "ldc %i \n" x

let lda x = sprintf "lda %i \n" x

let sta x = sprintf "sta %i \n" x

let op1code  = function
	| Not -> "not \n"
	| Neg -> "neg \n"

let some_funcallcode id arglength=
"bsr "^id^" \n"^
(sprintf "ajs -%i \n" arglength)^
"ldr RR \n"

let none_funcallcode id arglength=
"bsr "^id^" \n"^
(sprintf "ajs -%i \n" arglength)

let op2code = function
	| Listop ->  listappendcode
	| Logop And -> "and \n"
	| Logop Or -> "or \n"
	| Eqop Eq -> "eq \n"
	| Eqop Neq -> "ne \n"
	| Compop Less -> "lt \n"
	| Compop Greater -> "gt \n"
	| Compop LeEq -> "le \n"
	| Compop GrEq -> "ge \n"
	| Strongop Times -> "mul \n"
	| Strongop Divide -> "div \n"
	| Strongop Modulo -> "mod \n"
	| Weakop Plus -> "add \n"
	| Weakop Minus -> "sub \n"

let isempty_code =
"isEmpty: link 0 \n"^
"ldc 0 \n"^
"ldl -2 \n"^
"eq \n"^
"brf endifisempty \n"^
(sprintf "ldc %i \n" truenr)^
"str RR \n"^
"unlink \n"^
"ret \n"^
"endifisempty: ldc 0 \n"^
"str RR \n"^
"unlink \n"^
"ret \n"