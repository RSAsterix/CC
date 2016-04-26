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
(* emptylistplek is niet nodig. Een willekeurige waarde in r5 is genoeg. *)
(* + en - zijn ook defined voor char. ga er even van uit dat het niet defined moet worden voor andere types. Tom moet dit nog regelen *)
(* als r5 constant is, kan hij ook gwn in dit document geladen worden *)


(* besluiten *)
(* "var id = exp" betekent niks anders dan dat je geen zin had om de type van id te specificeren *) 
(* lists zijn single linkedlists, oftewel tuples van (waarde, pointer naar volgende plek) *)
(* //Er is een ongebruikte plek in de heap. Als een list hier naar point, is hij empty *)
(* Als een pointer is 0, dan wijst hij naar een lege lijst *)
(* R5 bevat het begin van de heap *)

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

let get_vartype id vars = 
	let vt = (try find (fun x -> fst x =id) vars with
	| Not_found -> ("henkst",Int))
	in snd vt
	
let get_funtype (id:id) funs = 
	try find (fun (x:functiontype) -> x.fid=id) funs with
	| Not_found -> empty_functiontype

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
	| Exp_field (Field (exp,Hd))
	| Exp_field (Field (exp,Fst)) -> (exp_gen vars (Exp_field exp)) ^ lda 0
	| Exp_field (Field (exp,Tl))
	| Exp_field (Field (exp,Snd)) -> (exp_gen vars (Exp_field exp)) ^ lda 1
	| Exp_infix (exp1,op,exp2) -> (exp_gen vars exp1) ^ (exp_gen vars exp2) ^ (op2code op)
	| Exp_prefix (op,exp) -> (exp_gen vars exp) ^ (op1code op)
	| Exp_function_call (id,explist) -> (list_gen (exp_gen vars) (explist)) ^ (some_funcallcode id (length explist))
	| Exp_emptylist -> ldc 0
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

let branchindex = ref 0;;

let choose_label labeloption label2 =
	match labeloption with
	| Some label1 -> label1
	| None -> label2

let rec if_gen vars fid nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let endiflabel = choose_label nalabeloption (endiflabel fid !branchindex) in
		let code =
  		exp_gen vars exp^
  		brf endiflabel^ 
  		stmtlist_gen vars fid None stmts^
  		pointlabel endiflabel in
		(code, None)
and
if_else_gen vars fid nalabeloption = function
	| (exp,stmtsif,stmtselse) -> branchindex := !branchindex + 1;
		let endiflabel = endiflabel fid !branchindex in
		let endelselabel = choose_label nalabeloption (endelselabel fid !branchindex) in
		let code =
  		exp_gen vars exp^
  		brf endiflabel^ 
  		stmtlist_gen vars fid None stmtsif^ 
  		bra endelselabel^ 
  		stmtlist_gen vars fid (Some endiflabel) stmtselse^
  		pointlabel endelselabel in
		(code,None)
and
while_gen vars fid startlabeloption nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let startwhilelabel = choose_label startlabeloption (startwhilelabel fid !branchindex) in
		let endwhilelabel = choose_label nalabeloption (endwhilelabel fid !branchindex) in
		let code =
			pointlabel startwhilelabel^
			exp_gen vars exp^
			brf endwhilelabel^
			stmtlist_gen vars fid None stmts^
			bra startwhilelabel^
			pointlabel endwhilelabel in
			(code,Some startwhilelabel)
and
define_gen vars = function
	| (Nofield id, exp) -> 
		let idstruct = get_idstruct id vars in
		let code =
			exp_gen vars exp^ 
			code_set idstruct in
			(code,None)
	| _ -> ("stmt_gen henk",None)
and
function_call_gen vars = function
	| (id,explist) -> 
		let code = 
			list_gen (exp_gen vars) explist^ 
			none_funcallcode id (length explist) in
			(code,None)
and
return_gen vars = function
	| (Some exp) -> 
		let code = 
			exp_gen vars exp^ 
			return_some_code in
			(code,None)
	| None -> 
		let code = 
			return_none_code in
			(code,None)
and
stmt_gen vars fid nalabeloption = function
	| Stmt_if (a,b) -> if_gen vars fid nalabeloption (a,b)
	| Stmt_if_else (a,b,c) -> if_else_gen vars fid nalabeloption (a,b,c)
	| Stmt_while (a,b) -> while_gen vars fid None nalabeloption (a,b)
	| Stmt_define (a,b) -> define_gen vars (a,b)
	| Stmt_function_call (a,b) -> function_call_gen vars (a,b)
	| Stmt_return a -> return_gen vars a
and
stmtlist_gen vars fid startlabel stmtlist = 
	let rec stmtlist_gen' vars fid = function
  	| stmt::stmtlist -> 
  		let (stmtlistcode,nalabeloption) = stmtlist_gen' vars fid stmtlist in
  		let (stmtcode,nalabeloption) = stmt_gen vars fid nalabeloption stmt in
  		(stmtcode^stmtlistcode,nalabeloption)
  	| [] -> ("",None) in
	match stmtlist with
	| (Stmt_while (a,b))::stmtlist -> 
		let (stmtlistcode,nalabeloption) = stmtlist_gen' vars fid stmtlist in
		let (whilecode,_) = while_gen vars fid startlabel nalabeloption (a,b) in
		whilecode ^ stmtlistcode
	| stmtlist -> 
		let (stmtlistcode,_) = stmtlist_gen' vars fid stmtlist in
		match startlabel with
		| Some startlabel -> pointlabel startlabel ^ stmtlistcode
		| None -> stmtlistcode

let last_if_else_gen vars fid nalabeloption = function
	| (exp,stmtsif,stmtselse) -> branchindex := !branchindex + 1;
	let endiflabel = endiflabel fid !branchindex in
	let code =
		exp_gen vars exp^
		brf endiflabel^ 
		stmtlist_gen vars fid None stmtsif^ 
		stmtlist_gen vars fid (Some endiflabel) stmtselse in
	(code,None)

let last_while_gen vars fid startlabeloption nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let startwhilelabel = choose_label startlabeloption (startwhilelabel fid !branchindex) in
		let code =
			stmtlist_gen vars fid (Some startwhilelabel) stmts^
			bra startwhilelabel in
			(code,Some startwhilelabel)

let last_stmt_gen vars fid nalabeloption = function
	| Stmt_if_else (a,b,c) -> last_if_else_gen vars fid nalabeloption (a,b,c)
	| Stmt_while (a,b) -> last_while_gen vars fid None nalabeloption (a,b)
	| stmt -> stmt_gen vars fid nalabeloption stmt

let topstmtlist_gen vars fid startlabel stmtlist =
	let rec topstmtlist_gen' vars fid = function
		| stmt::[] -> last_stmt_gen vars fid None stmt
  	| stmt::stmtlist -> 
  		let (stmtlistcode,nalabeloption) = topstmtlist_gen' vars fid stmtlist in
  		let (stmtcode,nalabeloption) = stmt_gen vars fid nalabeloption stmt in
  		(stmtcode^stmtlistcode,nalabeloption)
  	| [] -> ("",None) in
	match stmtlist with
	| (Stmt_while (a,b))::[] -> 
		let (whilecode,_) = last_while_gen vars fid startlabel None (a,b) in
		whilecode
	| (Stmt_while (a,b))::stmtlist -> 
		let (stmtlistcode,nalabeloption) = topstmtlist_gen' vars fid stmtlist in
		let (whilecode,_) = while_gen vars fid startlabel nalabeloption (a,b) in
		whilecode ^ stmtlistcode
	| stmtlist -> 
		let (stmtlistcode,_) = topstmtlist_gen' vars fid stmtlist in
		match startlabel with
		| Some startlabel -> pointlabel startlabel ^ stmtlistcode
		| None -> stmtlistcode
		
let rec fargs_to_idstructs  i fargtypes = function
	| id::fargs -> {global=false;vartype=hd fargtypes; id=id; index=i}::(fargs_to_idstructs (i-1) (tl fargtypes) fargs) 
	| [] -> []

let rec vardecl_gen vars = function
	|(t,id,exp)::vardecllist -> 
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

let varlength = ref 0;;

let rec get_vars global i vartypes = function
	| (None,id,_)::decllist -> get_vars global i vartypes decllist
	| (Some _,id,_)::decllist -> 
		let idstruct = {global=global;vartype=get_vartype id vartypes; id=id; index=i} in 
		(match idstruct.vartype with
		| Lis _ | Tup _ when idstruct.global=true -> idstruct::(get_vars global (i+2) vartypes decllist)
		| _ -> idstruct::(get_vars global (i+1) vartypes decllist))
	| [] -> varlength = ref i; []
	| _::decllist -> get_vars global i vartypes decllist

let rec print_vars = function
	| var::vars -> var.id ^ " " ^ (print_vars vars)
	| [] -> " # "

let rec ftype_to_fargtypes=function
	| Imp (t,ftype) -> t::ftype_to_fargtypes ftype

(* in order: *)
(* set branchname*)
(* reserve space for the local vars *)
(* parse the local vars *)
(* parse de stmts. This includes return *)
let rec functions_gen (gvars:'a list) funtypes vartypes = function
	| (fid,fargs,_,vardecllist,stmtlist)::decllist ->
		let funtype = get_funtype fid funtypes in
		let fargtypes = ftype_to_fargtypes funtype.ftype in
		let fargs = fargs_to_idstructs (-1-(length fargs)) fargtypes fargs  in
		let lvars = get_vars false 1 vartypes vardecllist in
		let localknown = localknown fargs lvars gvars in
			pointlabel fid^
  		reservelocalcode (length lvars)^
  		vardecl_gen localknown vardecllist^
  		topstmtlist_gen localknown fid None stmtlist^
  		functions_gen gvars funtypes vartypes decllist
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
let code_gen vartypes funtypes (spl:decl list) = 
	let mainlabel = "main" in
	let gvars = get_vars true 0 vartypes (get_vardecls spl) in
	let gvarlength = !varlength in  
		bra mainlabel^
		functions_gen gvars funtypes vartypes (get_fundecls spl)^ 
		pointlabel mainlabel^ 
		reservecode (!varlength)^ 
		vardecl_gen gvars (get_vardecls spl)


