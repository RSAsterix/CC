open Printf
open Types

let reserve_emptylistcode = 
"ldc 0 \n"^
"sth \n"^
"str R5 \n"


let ifcode fid i = sprintf "brf endif%s%i \n" fid i
let endifcode fid i = sprintf "endif%s%i " fid i
let elsecode fid i = sprintf "bra endelse%s%i \n" fid i
let endelsecode fid i = sprintf "endelse%s%i " fid i
let beforewhilecode fid i= sprintf "startwhile%s%i " fid i
let whilecode fid i = sprintf "brt endwhile%s%i \n" fid i
let endwhilecode fid i = 
	(sprintf "bra startwhile%s%i \n" fid i)^
	(sprintf "endwhile%s%i \n" fid i)

let branch_to_maincode ="bra main \n"

let reservelocalcode i = sprintf "link %i \n" i

let rec reservecode i = 
"ldr HP \n"^
(sprintf "ldc %i \n" i)^ 
"add \n"^
"str HP \n"

type idstruct = {
	global: bool;
	basic: bool;
	id: string;
	index: int;
	}

let code_set id = 
	if id.global then
		"ldr R5 \n"^
		(sprintf "sta %i \n" id.index)
	else
		sprintf "stl %i \n" id.index

let code_get id =
	if id.global then
		"ldr R5 \n"^
		(sprintf "lda %i \n" id.index)
	else
		sprintf "ldl %i \n" id.index
		
let return_some_code arglength = 
  "str RR \n"^
	"unlink \n"^
	(sprintf "ajs -%i" arglength)^
	"ret \n"

let return_none_code arglength =sprintf 
  "unlink \n"^
	(sprintf "ajs -%i" arglength)^
	"ret \n"

let firstof_code ="ldh 0 \n"

let secondof_code ="ldh 1 \n"

(* De nieuwe headwaarde en de oude listpointer staan al op de stack *)
(* returnt de nieuwe listpointer *)
let listappendcode = "stmh 2 \n"	

let create_tuplecode ="stmh 2 \n"

let ldc x = sprintf "ldc %i \n" x

let get_emptylistcode ="ldr r5 \n"

let op1code  = function
	| Not -> "not \n"
	| Neg -> "neg \n"

let some_funcallcode id =
"ldr RR \n"^
"bsr "^id^" \n"

let none_funcallcode id ="bsr "^id^" \n"

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