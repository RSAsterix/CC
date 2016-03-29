open String
open Types
open Char
open Codefragments
open List
open Pretty_printer_files
	
let list_gen (gen:'a->string) (alist:'a list): string = fold_right (^) (map gen alist) ("")

(* TODO: *)
(* it should be possible to use functions and global variables before they are defined *)
(* onze tokenizer moet comments wegmieteren *)
(* checken of een functie altijd returnt? *)
(* exp_gen kan alleen nog maar global vars aan *)
(* adding something to a list creates a whole new list *)
(* load return register staat voor de branch *)


(* besluiten *)
(* "var id = exp" betekent niks anders dan dat je geen zin had om de type van id te specificeren *) 
(* lists zijn single linkedlists, oftewel tuples van (waarde, pointer naar volgende plek) *)
(* Er is een ongebruikte plek in de heap. Als een list hier naar point, is hij empty *)

(* open Set  *)


(* module Id =                 *)
(*   struct                 *)
(*    type t = int * string         *)
(*    let compare (x0,y0) (x1,y1) =     *)
(*     match Pervasives.compare y0 y1 with *)
(*      | 0 -> Pervasives.compare x0 x1  *)
(*      | c -> c             *)
(*   end                   *)

(* module Ids = Set.Make(Id)          *)

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
(* //Als een lijst of tuple gedeclareerd wordt, reserveer 2 plekken *)
(* Het is vele malen handiger om een pointer hiervoor neer te zetten *)
(* Skip idtypes voor nu *)

(* exp_infix voorbeeld *)
(* 2 + 3 *)
(*LDC	2
	LDC	3
	ADD *)

let get_idstruct id vars = 
	try find (fun x -> x.id=id) vars with
	| Not_found -> empty_idstruct

(* Deze functie gaat er nog even van uit dat alle vars global zijn *)
(* let rec field_gen vars = function                                        *)
(* 	| Nofield id -> let idstruct = get_idstruct id vars in                 *)
(* 		if idstruct.basic then                                               *)
(* 			global_basic_var_address                                           *)
(* 		else                                                                 *)
(* 			global_notbasic_var_address                                        *)
(* 	| Field (fieldexp, Hd)                                                 *)
(* 	| Field (fieldexp, Fst) -> (field_gen vars fieldexp) ^ get_first_code  *)
(* 	| Field (fieldexp, Tl)                                                 *)
(* 	| Field (fieldexp, Snd) -> (field_gen vars fieldexp) ^ get_second_code *)

let rec exp_gen vars exp =
	match exp with
	| Exp_int x -> ldc x
	| Exp_char x -> ldc (Char.code x)
	| Exp_bool true -> ldc 1
	| Exp_bool false -> ldc 0
	| Exp_field (Nofield id) -> let idstruct = get_idstruct id vars in code_get idstruct
	| Exp_field _ -> "exp_gen henk"
	| Exp_infix (exp1,op,exp2) -> (exp_gen vars exp1) ^ (exp_gen vars exp2) ^ (op2code op)
	| Exp_prefix (op,exp) -> (exp_gen vars exp) ^ (op1code op)
	| Exp_function_call (id,explist) -> (list_gen (exp_gen vars) (explist)) ^ (some_funcallcode id (length explist))
	| Exp_emptylist -> get_emptylistcode
	| Exp_tuple (exp1,exp2) -> (exp_gen vars exp1) ^ (exp_gen vars exp2) ^ create_tuplecode
	
(* sta: *)
(* Store via Address. *)
(* Pops 2 values from the stack and *)
(* stores the second popped value in the location pointed to by the first. *)
(* The pointer value is offset by a constant offset. *)


(* Wat moet er gebeuren met een vardecl (met een nieuw id)? *)
(* Zoek de var in de vars list en onthoud index i *)
(* '(var met index i) = x': *)
(* ldc x \n *)
(* ldr r5 \n *)
(* sta i \n *)

(* in order: *)
(* reserveer plek voor de localvars *)
(* parse de localvars *)
(* parse de stmts *)

let rec stmt_gen (vars: 'a list) (fid:string) (i:int) (stmt:stmt):(string*int) = match stmt with
	| Stmt_if (exp,stmts) -> 
		(match stmtlist_gen vars fid (i+1) stmts with
		| (code,j) -> (((exp_gen vars exp)^ (ifcode fid i) ^ (code) ^ (endifcode fid i)), j))
	| Stmt_if_else (exp,stmtsif,stmtselse) -> 
		(match stmtlist_gen vars fid (i+1) stmtsif with
		| (code1,j) ->
			(match stmtlist_gen vars fid (j+1) stmtselse with
			| (code2,k) -> ((exp_gen vars exp) ^ ifcode fid i ^ code1 ^ elsecode fid i ^ endifcode fid i ^ code2 ^endelsecode fid i, k)))
	| Stmt_while (exp,stmts) -> 
		(match stmtlist_gen vars fid (i+1) stmts with
		| (code,j) -> (beforewhilecode fid i^ (exp_gen vars exp) ^ whilecode fid i^ code ^ endwhilecode fid i, j))
	| Stmt_define (Nofield id,exp) -> let idstruct = get_idstruct id vars in ((exp_gen vars exp) ^ code_set idstruct, i)
	| Stmt_define _ -> ("stmt_gen henk",i)
	| Stmt_function_call (id,explist) -> ((list_gen (exp_gen vars) (explist)) ^ (none_funcallcode id (length explist)), i)
	| Stmt_return (Some exp) -> ((exp_gen vars exp) ^ (return_some_code),i)
	| Stmt_return None -> ((return_none_code),i)
and
stmtlist_gen (vars:'a list) (fid:string) (i:int) = function
	| stmt::stmtlist -> 
		(match stmt_gen vars fid i stmt with
		| (codehd,i) -> 
			(match stmtlist_gen vars fid i stmtlist with
			| (codetl,i) -> (codehd^codetl,i)))
	| [] -> ("",i)

let rec fargs_to_idstructs i = function
	| id::fargs -> {global=false;basic=true; id=id; index=i}::(fargs_to_idstructs (i+1) fargs) 
	| [] -> []

let rec vardecl_gen vars = function
	|(_,id,exp)::vardecllist -> 
		let id= get_idstruct id vars in
		(exp_gen vars exp) ^ (code_set id)^(vardecl_gen vars vardecllist)
	| [] -> ""

(* append_unique l1 l2: append el l2 als hij niet voorkomt in l1 *)
let rec append_unique l1 = function
	| el2::l2 -> 
		if mem el2 l1 then
			append_unique l1 l2
		else
			append_unique (el2::l1) l2
	| [] -> l1 

(* Als een var in fargs voorkomt bindt die sterker dan als in gvars *)
(* Als een var in lvars voorkomt en ook in fargs hoeft er geen ruimte voor gereserveerd te worden *)
let localknown fargs lvars gvars = append_unique lvars (append_unique fargs gvars)

let rec get_vars global i = function
	| (Some (Basictype _),id,_)::decllist
	| ((None),id,_)::decllist -> {global=global;basic=true; id=id; index=i}::(get_vars global (i+1) decllist)
	| [] -> []
	| _::decllist -> get_vars global i decllist

let rec print_vars = function
	| var::vars -> var.id ^ " " ^ (print_vars vars)
	| [] -> " # "

(* in order: *)
(* set branchname*)
(* reserve space for the local vars *)
(* parse the local vars *)
(* parse de stmts. This includes return *)
let rec functions_gen (gvars:'a list) = function
	| (fid,fargs,_,vardecllist,stmtlist)::decllist -> 
		let fargs = fargs_to_idstructs (-1-(length fargs)) fargs in
		let lvars = get_vars false 0 vardecllist in
		let localknown = localknown fargs lvars gvars in
		let stmtlistcode = fst (stmtlist_gen localknown fid 0 stmtlist) in 
		(* print_vars fargs ^ print_vars lvars ^ print_vars gvars ^ print_vars localknown ^ *)
		(fid ^": "^ (reservelocalcode (length lvars)) ^ (vardecl_gen localknown vardecllist) ^ stmtlistcode)^(functions_gen gvars decllist)
	| [] -> ""

let rec get_vardecls = function
	| (Vardecl vardecl)::spl -> vardecl::(get_vardecls spl)
	| (Fundecl fundecl)::spl -> get_vardecls spl
	| [] -> []

let rec get_fundecls = function
	| (Fundecl fundecl)::spl -> fundecl::(get_fundecls spl)
	| (Vardecl vardecl)::spl -> get_fundecls spl
	| [] -> []

let rec print_vardecls = function
	| (_,id,_)::list -> id ^" "^(print_vardecls list)
	| [] -> " # "
(* in order: *)
(* make the startcode: define emptylist and branch to main *)
(* reserve space for all global vars *)
(* define all functions *)
(* generate main: only look at vardecls *)
let code_gen (spl:decl list) = let gvars = get_vars true 1 (get_vardecls spl) in
	branch_to_maincode ^ (functions_gen gvars (get_fundecls spl)) ^ "main: "^ reserve_emptylistcode ^  (reservecode (length gvars)) ^ (vardecl_gen gvars (get_vardecls spl))

