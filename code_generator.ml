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


(* besluiten *)
(* "var id = exp" betekent niks anders dan dat je geen zin had om de type van id te specificeren *) 
(* lists zijn single linkedlists, oftewel tuples van (waarde, pointer naar volgende plek) *)
(* Er is een ongebruikte plek in de heap. Als een list hier naar point, is hij empty *)

(* global basic type: *)
(* 		in stack: pointer naar ergens begin heap *)
(* 		in heap: int *)
(* local basic type: *)
(*  	in stack: int value *)
(* 		in heap: - *)
(* global list: *)
(* 		in stack: pointer naar ergens begin heap *)
(* 		in heap: 10 plekken, *)
(* 				8 zijn listvalues behorend bij de index, *)
(* 				1 is de optionele pointer naar de rest van de list *)
(* 				1 is de lengte van de list, deze komt niet meer voor in de rest van de list *)
(* local list: *)
(* 		in stack: pointer naar heap *)
(* 		in heap: hetzelfde als global list *)
(* global tuple: *)
(* 		in stack: pointer naar ergens begin heap *)
(* 		in heap: 2x twee plekken met het volgende *)
(* 			boolean of de eerste value basic is, *)
(* 			als basic: int value, als nonbasic: pointer *)
(* local tuple: *)
(* 		in stack: pointer naar heap *)
(* 		in heap: hetzelfde als global tuple *)
(* id type: *)
(* 		ik weet niet precies wat deze type moet doen, *)
(* 		dus we doen wel alsof het een willekeurige andere type is. *)




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
	| (fid,fargs,types,vardecllist,stmtlist)::decllist -> 
		let fargs = fargs_to_idstructs (-1-(length fargs)) fargs in
		let lvars = get_vars false 1 vardecllist in
		let localknown = localknown fargs lvars gvars in
			pointlabel fid^
  		reservelocalcode (length lvars)^
  		vardecl_gen localknown vardecllist^
  		topstmtlist_gen localknown fid None stmtlist^
  		functions_gen gvars decllist
	| [] -> ""

let rec unpoly_typetokenlist = function
	| typetoken::list ->
		match typetoken with
		| Type_id "poly" ->
			let typetokenlistlist = unpoly_typetokenlist list in
			map (fun x -> Typ)

let rec unpoly_fundecllist = function
	| fundecl::list -> 
		match fundecl with
		| (id,fargs,Some (typetokenlist,rettype), vardecllist, stmtlist) -> 
			unpoly_typetokenlist

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
let code_gen (spl:decl list) = 
	let gvars = get_vars true 1 (get_vardecls spl) in
	let mainlabel = "main" in
		bra mainlabel^
		functions_gen gvars (unpoly_fundecllist (get_fundecls spl))^ 
		pointlabel mainlabel^ 
		reservecode (length gvars)^ 
		vardecl_gen gvars (get_vardecls spl)


