open String
open Types
open Char
open Codefragments
open List
open Pretty_printer_files
open Typechecker_types
	
let list_gen (gen:'a->string) (alist:'a list): string = fold_right (^) (map gen alist) ("");;

(* TODO: *)
(* checken of een functie altijd returnt? *)
(* gebruikmaken van registers *)


(* besluiten *)
(* "var id = exp" betekent niks anders dan dat je geen zin had om de type van id te specificeren *) 
(* lists zijn single linkedlists, oftewel tuples van (waarde, pointer naar volgende plek) *)
(* Als een pointer is 0, dan wijst hij naar een lege lijst *)

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

let get_vartype id (vars : env_var list) =
	try
		(List.find (fun (x : env_var) -> x.id = id) vars).t
	with
	| Not_found -> Void;;
	
let get_fun id (funs : env_fun list) =
	try
		(List.find (fun (x : env_fun) -> x.id=id) funs)
	with
	| Not_found -> empty_fun;;

let get_idstruct id (idstructs : idstruct list) =
	try 
		List.find (fun (x : idstruct) -> x.id=id) idstructs 
	with
	| Not_found -> empty_idstruct;;

let rec get_index p lst c = match lst with
    | [] -> raise(Not_found)
    | hd::tl -> if p hd then c else get_index p tl (c+1)

let rec get_cons cons c types =
	match types with
	| ((x,None)::resttype)::types when x=cons -> c
	| (hd::resttype)::types -> get_cons cons (c+1) (resttype::types)
	| []::types -> get_cons cons 0 types
	| [] -> -1

let rec expfield_gen vars = function
	| Nofield id -> let idstruct = get_idstruct id vars in code_get idstruct
	| Field (exp,Hd)
	| Field (exp,Fst) -> (expfield_gen vars exp) ^ lda (-1)
	| Field (exp,Tl)
	| Field (exp,Snd) -> (expfield_gen vars exp) ^ lda 0;;

let rec exp_gen vars types exp =
	match exp with
	| Exp_int x -> ldc x
	| Exp_char x -> ldc (Char.code x)
	| Exp_bool true -> ldc truenr
	| Exp_bool false -> ldc 0
	| Exp_field (expfield) -> expfield_gen vars expfield
	| Exp_infix (exp1,op,exp2) -> (exp_gen vars types exp1) ^ (exp_gen vars types exp2) ^ (op2code op)
	| Exp_prefix (op,exp) -> (exp_gen vars types exp) ^ (op1code op)
	| Exp_function_call (id,explist) -> (list_gen (exp_gen vars types) (explist)) ^ (some_funcallcode id (length explist))
	| Exp_emptylist -> ldc 0
	| Exp_tuple (exp1,exp2) -> (exp_gen vars types exp1) ^ (exp_gen vars types exp2) ^ create_tuplecode
	| Exp_constructor x -> ldc (get_cons x 0 types)
	| Exp_low_bar -> raise Not_found;;
	
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

let rec if_gen vars types fid nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let endiflabel = choose_label nalabeloption (endiflabel fid !branchindex) in
		let code =
  		exp_gen vars types exp^
  		brf endiflabel^ 
  		stmtlist_gen vars types fid None stmts^
  		pointlabel endiflabel in
		(code, None)
and
if_else_gen vars types fid nalabeloption = function
	| (exp,stmtsif,stmtselse) -> branchindex := !branchindex + 1;
		let endiflabel = endiflabel fid !branchindex in
		let endelselabel = choose_label nalabeloption (endelselabel fid !branchindex) in
		let code =
  		exp_gen vars types exp^
  		brf endiflabel^ 
  		stmtlist_gen vars types fid None stmtsif^ 
  		bra endelselabel^ 
  		stmtlist_gen vars types fid (Some endiflabel) stmtselse^
  		pointlabel endelselabel in
		(code,None)
and
while_gen vars types fid startlabeloption nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let startwhilelabel = choose_label startlabeloption (startwhilelabel fid !branchindex) in
		let endwhilelabel = choose_label nalabeloption (endwhilelabel fid !branchindex) in
		let code =
			pointlabel startwhilelabel^
			exp_gen vars types exp^
			brf endwhilelabel^
			stmtlist_gen vars types fid None stmts^
			bra startwhilelabel^
			pointlabel endwhilelabel in
			(code,Some startwhilelabel)
and
define_gen vars types = function
	| (Nofield id, exp) -> 
		let idstruct = get_idstruct id vars in
		let code =
			exp_gen vars types exp^ 
			code_set idstruct in
			(code,None)
	| (Field (fieldexp,Fst),exp)
	| (Field (fieldexp,Hd),exp) -> 
		let code = 
			exp_gen vars types exp^
			expfield_gen vars fieldexp ^
			sta (-1) in
		(code,None)
	| (Field (fieldexp,Snd),exp)
	| (Field (fieldexp,Tl),exp) ->
		let code = 
			exp_gen vars types exp^
			expfield_gen vars fieldexp ^
			sta 0 in
		(code, None)
and
function_call_gen vars types = function
	| (id,explist) -> 
		let code = 
			list_gen (exp_gen vars types) explist^ 
			none_funcallcode id (length explist) in
			(code,None)
and
return_gen vars types = function
	| (Some exp) -> 
		let code = 
			exp_gen vars types exp^ 
			return_some_code in
			(code,None)
	| None -> 
		let code = 
			return_none_code in
			(code,None)
and
stmt_gen vars types fid nalabeloption = function
	| Stmt_if (a,b) -> if_gen vars types fid nalabeloption (a,b)
	| Stmt_if_else (a,b,c) -> if_else_gen vars types fid nalabeloption (a,b,c)
	| Stmt_while (a,b) -> while_gen vars types fid None nalabeloption (a,b)
	| Stmt_define (a,b) -> define_gen vars types (a,b)
	| Stmt_function_call (a,b) -> function_call_gen vars types (a,b)
	| Stmt_return a -> return_gen vars types a
and
stmtlist_gen vars types fid startlabel stmtlist = 
	let rec stmtlist_gen' vars types fid = function
  	| stmt::stmtlist -> 
  		let (stmtlistcode,nalabeloption) = stmtlist_gen' vars types fid stmtlist in
  		let (stmtcode,nalabeloption) = stmt_gen vars types fid nalabeloption stmt in
  		(stmtcode^stmtlistcode,nalabeloption)
  	| [] -> ("",None) in
	match stmtlist with
	| (Stmt_while (a,b))::stmtlist -> 
		let (stmtlistcode,nalabeloption) = stmtlist_gen' vars types fid stmtlist in
		let (whilecode,_) = while_gen vars types fid startlabel nalabeloption (a,b) in
		whilecode ^ stmtlistcode
	| stmtlist -> 
		let (stmtlistcode,_) = stmtlist_gen' vars types fid stmtlist in
		match startlabel with
		| Some startlabel -> pointlabel startlabel ^ stmtlistcode
		| None -> stmtlistcode

let last_if_else_gen vars types fid nalabeloption = function
	| (exp,stmtsif,stmtselse) -> branchindex := !branchindex + 1;
	let endiflabel = endiflabel fid !branchindex in
	let code =
		exp_gen vars types exp^
		brf endiflabel^ 
		stmtlist_gen vars types fid None stmtsif^ 
		stmtlist_gen vars types fid (Some endiflabel) stmtselse in
	(code,None)

let last_while_gen vars types fid startlabeloption nalabeloption = function
	| (exp,stmts) -> branchindex := !branchindex + 1;
		let startwhilelabel = choose_label startlabeloption (startwhilelabel fid !branchindex) in
		let code =
			stmtlist_gen vars types fid (Some startwhilelabel) stmts^
			bra startwhilelabel in
			(code,Some startwhilelabel)

let last_stmt_gen vars types fid nalabeloption = function
	| Stmt_if_else (a,b,c) -> last_if_else_gen vars types fid nalabeloption (a,b,c)
	| Stmt_while (a,b) -> last_while_gen vars types fid None nalabeloption (a,b)
	| stmt -> stmt_gen vars types fid nalabeloption stmt

let topstmtlist_gen vars types fid startlabel stmtlist =
	let rec topstmtlist_gen' vars types fid = function
		| stmt::[] -> last_stmt_gen vars types fid None stmt
  	| stmt::stmtlist -> 
  		let (stmtlistcode,nalabeloption) = topstmtlist_gen' vars types fid stmtlist in
  		let (stmtcode,nalabeloption) = stmt_gen vars types fid nalabeloption stmt in
  		(stmtcode^stmtlistcode,nalabeloption)
  	| [] -> ("",None) in
	match stmtlist with
	| (Stmt_while (a,b))::[] -> 
		let (whilecode,_) = last_while_gen vars types fid startlabel None (a,b) in
		whilecode
	| (Stmt_while (a,b))::stmtlist -> 
		let (stmtlistcode,nalabeloption) = topstmtlist_gen' vars types fid stmtlist in
		let (whilecode,_) = while_gen vars types fid startlabel nalabeloption (a,b) in
		whilecode ^ stmtlistcode
	| stmtlist -> 
		let (stmtlistcode,_) = topstmtlist_gen' vars types fid stmtlist in
		match startlabel with
		| Some startlabel -> pointlabel startlabel ^ stmtlistcode
		| None -> stmtlistcode
		
let rec fargs_to_idstructs  i fargtypes = function
	| id::fargs -> {global=false;vartype=hd fargtypes; id=id; index=i}::(fargs_to_idstructs (i+1) (tl fargtypes) fargs) 
	| [] -> []

let rec vardecl_gen vars types = function
	|(t,id,exp)::vardecllist -> 
		let id= get_idstruct id vars in
		(exp_gen vars types exp) ^ (code_set id)^(vardecl_gen vars types vardecllist)
	| [] -> ""

(* append_unique l1 l2: append el l2 als hij niet voorkomt in l1 *)
let rec append_unique (l1: idstruct list) (l2: idstruct list) = match l2 with
	| el2::l2 -> 
		if List.exists (fun (x: idstruct) -> x.id = el2.id) l1
		then
			append_unique l1 l2
		else
			append_unique (el2::l1) l2
	| [] -> l1 

(* Als een var in fargs voorkomt bindt die sterker dan als in gvars*)
(* Als een var in lvars voorkomt en ook in fargs hoeft er geen ruimte voor gereserveerd te worden *)
let localknown fargs lvars gvars = append_unique lvars (append_unique fargs gvars)

let rec vartypes_to_idstructs global index = function
	| (x : env_var)::vartypes -> {id=x.id;vartype=x.t;global=global;index=index}::vartypes_to_idstructs global (index+1) vartypes
	| [] -> []

let rec print_vars = function
	| var::vars -> var.id ^ " " ^ (print_vars vars)
	| [] -> " # "

let rec ftype_to_fargtypes=function
	| Imp (t,ftype) -> t::ftype_to_fargtypes ftype
	| _ -> []

(* in order: *)
(* set branchname*)
(* reserve space for the local vars *)
(* parse the local vars *)
(* parse de stmts. This includes return *)
let functions_gen (gvars:'a list) funtypes vartypes types = function
	| (fid,fargs,_,vardecllist,stmtlist)::decllist ->
		let func = get_fun fid funtypes in
		let fargtypes = ftype_to_fargtypes func.t in
		let fargs = fargs_to_idstructs (-1-(length fargs)) fargtypes fargs in
		let locals = Env_var.fold (fun x list ->
			if (List.exists (fun (y: idstruct) -> y.id = x.id) fargs)
			then list
			else x::list) func.locals [] in
		let lvars = vartypes_to_idstructs false 1 locals in
		let localknown = localknown fargs lvars gvars in
			pointlabel fid^
  		reservelocalcode (length lvars)^
  		vardecl_gen localknown vardecllist types^
  		topstmtlist_gen localknown types fid None stmtlist^
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
let code_gen env (spl:decl list) = 
	let vartypes = Env_var.elements env.vars in
	let funtypes = Env_fun.elements env.funs in
	let typedefs = fst Env_type.elements env.types in
	let mainlabel = "main" in
	let gvars = vartypes_to_idstructs true 0 vartypes in
		typedefs ^ 
		reservecode (length gvars)^ 
		vardecl_gen gvars (get_vardecls spl)^
		"bsr "^ mainlabel^" \n"^
		end_code^
		functions_gen gvars funtypes vartypes typedefs (get_fundecls spl)^
		isempty_code^ 
		read_code^
		write_code
		

		

