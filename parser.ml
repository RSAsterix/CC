open Char_func
open Types
open Printf
open Tokenizer
open Exp_parser


(* type =    basictype       *)
(* 		| id                  *)
(* 		| '(' type , type ')' *)
(* 		| '[' type ']'        *)
(* basictype = 'Int' | 'Bool' | 'Char' *)
let rec type_parser = function
	| (_,Basic_int)::list -> Success (Type_int),list
	| (_,Basic_bool)::list -> Success (Type_bool),list
	| (_,Basic_char)::list -> Success (Type_char),list
	| (_,IDtok id)::list -> Success (Type_id id),list
	| (l0,OPEN_PAR)::list -> 
		(match (type_parser list) with
		| Success type1, (l1,COMMA)::list -> 
			(match (type_parser list) with
			| Success type2, (_,CLOSE_PAR)::list -> Success (Type_tuple (type1,type2)),list
			| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis, but: %s" l (token_to_string x)), (l,x)::list
			| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after comma." l1), []
			| Error e, list -> Error e, list)
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after comma." l0), []
		| Error e, list -> Error e, list)
	| (l0,OPEN_BRACK)::list -> 
		(match (type_parser list) with
		| Success type1, (_,CLOSE_BRACK)::list -> Success (Type_list type1), list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing bracket, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after opening bracket." l0), [] 
		| Error e, list -> Error e, list)
	| (l,x)::list -> Error (sprintf "(r.%i) Unexpected token when expecting type: %s" l (token_to_string x)), (l,x)::list
	| [] -> Error "Unexpected EOF while parsing type.", [];;

(* rettype = 'Void' | type *)
let rettype_parser = function
	| (_,VOID)::list -> Success Type_void, list
	| list -> 
		(match type_parser list with
		| Success type1, list -> Success (Rettype type1), list
		| Error e, list -> Error e, list);;

(* varDeclRest = id '=' exp ';' *)
let rec funtype_parser type_list = function
  | (_,ARROW)::list	-> 
		(match rettype_parser list with
  	| Success rettype, list -> Success ((List.rev type_list), rettype), list
  	| Error e, list -> Error e, list)
  | list -> 
		(match type_parser list with
  	| Success type1, list -> funtype_parser (type1::type_list) list
		| Error e, list -> Error e, list);;

(* varDeclRest = id '=' exp ';' *)
let message = "If this is a variable declaration, you probably forgot the type or the 'var' keyword.";;
let vardecl_rest_parser typetoken = function
	| (_,IDtok id)::(l0,EQ)::list -> 
		(match exp_parser list with
		| Success exp, (_,SEMICOLON)::list -> Success (typetoken, id, exp), list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No semicolon, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after '='." l0), []   
		| Error e, list -> Error e, list)
	| (_,IDtok id)::(l,x)::list -> Error (sprintf "(r.%i) No '=', but: %s" l (token_to_string x)), (l,x)::list
	| (l,EQ)::list -> Error (sprintf "(r.%i) No id, but '=' detected.\n%s" l message), (l,EQ)::list
	| (l,x)::list -> Error (sprintf "(r.%i) No id, but: %s" l (token_to_string x)), (l,x)::list
	| [] -> Error "Unexpected EOF when parsing the rest of the variable declaration.", []

(* VarDecl = 'var' VarDeclRest *)
(* 		| type VarDeclRest      *)
let vardecl_parser = function
  | (_,VAR)::list -> vardecl_rest_parser None list
  | list -> 
		(match type_parser list with
		| Success type1, list -> vardecl_rest_parser (Some type1) list
		| Error e, list -> Error e, list);;

(* vardeclList = varDecl* *)
let rec vardecl_list_parser vardecl_list = function
	| list ->
		(match vardecl_parser list with
		| Error e, _ -> Success (List.rev vardecl_list), list
		| Success vardecl, list -> vardecl_list_parser (vardecl::vardecl_list) list);; 

(* stmtList = '}' | stmt stmtList                              *)
(* stmt =   'if' '(' exp ')' '{' stmtList 'else' '{' stmtList  *)
(* 		| 'if' '(' exp ')' '{' stmtList                         *)
(* 		| 'while' '(' exp ')' '{' stmtList                      *)
(* 		| 'return' ';'                                          *)
(* 		| 'return' exp ';'                                      *)
(* 		| id '(' funcall                                        *)
(* 		| id field '=' exp                                      *)
let rec stmt_list_parser stmt_list = function
	| (_,CLOSE_ACO)::list -> Success (List.rev stmt_list), list 
	| list ->
		(match stmt_parser list with
		| Success stmt, list -> stmt_list_parser (stmt::stmt_list) list
		| Error e, list -> Error e, list)
and
case_parser list = 
	match stelling_parser list with
	| Success stelling, (_,WHEN)::list ->
		(match exp_parser list with
		| Success predicate, (_,ARROW)::(_,OPEN_ACO)::list ->
			(match stmt_list_parser [] list with
			| Success stmt_list, list -> Success (stelling,Some predicate,stmt_list), list
			| Error e, list -> Error e, list)
		| Success predicate, (l,x)::list -> Error (sprintf "(r.%i) No arrow and open acolade, but: %s" l (token_to_string x)), (l,x)::list
		| Success predicate, [] -> Error "Unexpected EOF when expecting arrow.", []
		| Error e, list -> Error e, list)
	| Success stelling, (_,ARROW)::(_,OPEN_ACO)::list -> 
		(match stmt_list_parser [] list with
		| Success stmt_list, list -> Success (stelling,None,stmt_list), list
		| Error e, list -> Error e, list)
	| Success stelling, (l,x)::list -> Error (sprintf "(r.%i) No arrow and open acolade, but: %s" l (token_to_string x)), (l,x)::list
	| Success stelling, [] -> Error "Unexpected EOF when expecting arrow.", [] 
	| Error e, list -> Error e, list
and
case_list_parser case_list list =
  	match case_parser list with
  	| Success (stelling,predicate,stmt_list), (_,PIPE)::list -> case_list_parser ((stelling,predicate,stmt_list)::case_list) list
  	| Success (stelling,predicate,stmt_list), list -> Success (List.rev ((stelling,predicate,stmt_list)::case_list)), list
  	| Error e, list -> Error e, list
and
stmt_parser = function
	| (_,MATCH)::list ->
		(match exp_parser list with
		| Success exp, (_,WITH)::(_,PIPE)::list ->
			(match case_list_parser [] list with
			| Success case_list, list -> Success (Stmt_match (exp,case_list)), list
			| Error e, list -> Error e, list)
		| Success exp, (l,x)::list -> Error (sprintf "(r.%i) No 'with' keyword, but: %s" l (token_to_string x)), (l,x)::list
		| Success exp, [] -> Error "(r.%i) Unexpected EOF when expecting 'with' keyword.", [] 
		| Error e, list -> Error e, list)
  | (_,IF)::(l0,OPEN_PAR)::list ->
  	(match exp_parser list with
		| Success exp, (_,CLOSE_PAR)::(_,OPEN_ACO)::list ->
			(match stmt_list_parser [] list with
			| Success stmt_list1, (_,ELSE)::(_,OPEN_ACO)::list ->
				(match stmt_list_parser [] list with
				| Success stmt_list2, list -> Success (Stmt_if_else (exp, stmt_list1, stmt_list2)), list
				| Error e, list -> Error e, list)
			| Success _, (_,ELSE)::(l,x)::list -> Error (sprintf "(r.%i) No opening acolade, but: %s" l (token_to_string x)), (l,x)::list
			| Success _, (l,ELSE)::[] -> Error (sprintf "(r.%i) Unexpected EOF after 'else'." l), (l,ELSE)::[] 
			| Success stmt_list1, list -> Success (Stmt_if (exp, stmt_list1)), list
			| Error e, list -> Error e, list)
		| Success _, (_,CLOSE_PAR)::(l,x)::list -> Error (sprintf "(r.%i) No opening acolade, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, (l,CLOSE_PAR)::[] -> Error (sprintf "(r.%i) Unexpected EOF after closing parenthesis." l), (l,CLOSE_PAR)::[]
		| Success _, (l,x)::list -> Error (sprintf "(r.%i)  No closing parenthesis, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after opening parenthesis." l0), []
		| Error e, list -> Error e, list)
	| (_,WHILE)::(l0,OPEN_PAR)::list ->
		(match exp_parser list with
		| Success exp, (_,CLOSE_PAR)::(_,OPEN_ACO)::list ->
			(match stmt_list_parser [] list with
			| Success stmt_list, list -> Success (Stmt_while (exp, stmt_list)), list
			| Error e, list -> Error e, list)
		| Success _, (_,CLOSE_PAR)::(l,x)::list -> Error (sprintf "(r.%i) No opening acolade, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, (l,CLOSE_PAR)::[] -> Error (sprintf "(r.%i) Unexpected EOF after closing parenthesis." l), (l,CLOSE_PAR)::[]
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after opening parenthesis." l0), [] 
		| Error e, list -> Error e, list)
	| (_,RETURN)::(_,SEMICOLON)::list -> Success (Stmt_return(None)), list
	| (l0,RETURN)::list ->
		(match exp_parser list with
		| Success exp, (_,SEMICOLON)::list -> Success (Stmt_return(Some(exp))), list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No semicolon, but: %s" l (token_to_string x)), list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing 'return'." l0), [] 
		| Error e, list -> Error e, list)
	| (l0,IDtok id)::(_,OPEN_PAR)::list -> 
  	(match funcall_parser list with
  	| Success exp_list, (_,SEMICOLON)::list -> Success (Stmt_function_call ("$" ^ id, exp_list)), list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No semicolon, but: %s" l (token_to_string x)), list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing 'return'." l0), []
		| Error e, list -> Error e, list)
	| (l0,IDtok id)::list ->
		(match (field_parser [] list) with
		| Success fieldlist, (l1,EQ)::list ->
			(let rec packer = function
				| [] -> (Nofield id)
				| f::rest -> Field (packer rest, f) in
    	(match exp_parser list with
    	| Success exp, (_,SEMICOLON)::list ->
				Success (Stmt_define (packer fieldlist, exp)), list
    	| Success _, (l,x)::list -> Error (sprintf "(r.%i) No semicolon, but: %s" l (token_to_string x)), (l,x)::list
			| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing '='." l1), []   
			| Error e, list -> Error e, list))
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No '=', but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing %s" l0 id), []
		| Error e, list -> Error e, list)
	| (l,x)::list -> Error (sprintf "(r.%i) Unexpected token in stmt: %s" l (token_to_string x)), (l,x)::list
	| [] -> Error "Unexpected EOF while parsing statement.", []

(* fargs =   ')' | fargs2          *)
(* fargs2 = id ')' | id ',' fargs2 *)
(*opgesplitst in twee functies, zodat fargs ook '()' mag zijn*)
let fargs_parser list =
	let rec fargs2_parser id_list = function
		| (_,IDtok id)::(_,CLOSE_PAR)::list	-> Success (List.rev  (id::id_list)),list
  	| (_,IDtok id)::(_,COMMA)::list -> fargs2_parser (id::id_list) list
		| (_,IDtok id)::(l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis or comma, but: %s" l (token_to_string x)), (l,x)::list
		| (l,x)::list -> Error (sprintf "(r.%i) No id, but: %s" l (token_to_string x)), (l,x)::list
		| [] -> Error "Unexpected EOF when parsing function arguments.", []
  in match list with
	| (_,CLOSE_PAR)::list -> Success [], list
	| list -> fargs2_parser [] list

(* funDecl = fargs '(' vardeclList stmt stmtList     *)
(* 		| fargs '::' funtype '(' vardeclList stmtList *)
let fundecl_parser id list = match fargs_parser list with
  | Error e, list -> Error e, list
  | Success fargs, (l0,OPEN_ACO)::list ->
  	(match vardecl_list_parser [] list with
		| Error e, list -> Error e, list
  	| Success vardecl_list, list ->
  		(match stmt_list_parser [] list with
			| Error e, (l,VAR)::list -> Error (sprintf "(r.%i) Previous variable decleration parse failed, with error:\n%s" l e), list
  		| Error e, list -> Error e, list
  		| Success [], (l,x)::list -> Error (sprintf "(r.%i) Not the beginning of a statement, but: %s" l (token_to_string x)), (l,x)::list
			| Success [], [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing opening acolade." l0), [] 
  		| Success stmt_list, list -> Success (id, fargs, None, vardecl_list, stmt_list), list))
  | Success fargs, (l0,DDPOINT)::list ->
    (match funtype_parser [] list with
    | Error e, list -> Error e, list
    | Success funtype, (l1,OPEN_ACO)::list ->
      (match vardecl_list_parser [] list with
			| Error e, list -> Error e, list
      | Success vardecl_list, list ->
        (match stmt_list_parser [] list with
				| Error e, (l,VAR)::list -> Error (sprintf "(r.%i) Previous variable declaration parse failed, with error:\n%s" l e), list
        | Error e, list -> Error e, list
        | Success [], (l,x)::list -> Error (sprintf "(r.%i) No statement, but: %s" l (token_to_string x)), (l,x)::list
				| Success [], [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing opening acolade." l0), [] 
        | Success stmt_list, list -> Success (id, fargs, Some funtype, vardecl_list, stmt_list), list))
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No opening acolade, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing '::'." l0), [])
	| Success _, (l,x)::list -> Error (sprintf "(r.%i) No opening parenthesis or '::', but: %s" l (token_to_string x)), (l,x)::list
	| Success _, [] -> Error "Unexpected EOF while parsing function declaration.", [];;

(* (renames: (constructor * typetoken) list) *)
(* (enums: (constructor * int) list) *)

let rec enum_parser enumlist = function
	| (_,Constructortok c)::(_,PIPE)::list -> enum_parser (c::enumlist) list
	| (_,Constructortok c)::list -> Success (List.rev (c::enumlist)), list
	| (l,x)::list -> Error (sprintf "(r.%i) No enum, but: %s" l (token_to_string x)), (l,x)::list
	| [] -> Error "Unexpected EOF after parsing '|'.", []

let rec rename_parser id list =
	match type_parser list with
	| Success typetoken, list -> Success (Rename (id,typetoken)), list
	| Error e, list -> Error e, list

let typedecl_parser id = function
	| (_,Constructortok c)::(_,PIPE)::list ->
		(match enum_parser [] list with
		| Success enumlist, list -> Success (Enum (id,c::enumlist)),list
		| Error e, list -> Error e, list)
	| list -> 
		(match rename_parser id list with
		| Success rename, list -> Success rename, list
		| Error e, list -> Error e, list)

(* Decl = id '('  FunDecl | VarDecl *)
let decl_parser = function
	| (_,IDtok id)::(_,OPEN_PAR)::list ->
		(match fundecl_parser ("$" ^ id) list with
		| Success fundecl, list -> Success (Fundecl fundecl), list
		| Error e, faillist -> Error e, faillist)
	| (l,IDtok id)::[] -> Error (sprintf "(r.%i) Unexpected EOF after parsing id.\nBy the way: is '%s' a type for a variable, or a function name without arguments?" l id), []
	| list -> 
		(match vardecl_parser list with
		| Success vardecl, list -> Success (Vardecl vardecl), list
		| Error e, faillist -> Error e, faillist);;

let rec remove_comments = function
	| (l,Startcomment)::list -> remove_comments' list
	| (l,token)::list -> 
		(match remove_comments list with
		| Success list -> Success ((l,token)::list)
		| Error e -> Error e)
	| [] -> Success []
and
remove_comments' = function
	| (l,Endcomment)::list -> remove_comments list
	| (l,token)::list -> remove_comments' list
	| [] -> Error "comment does not end"

let rec decllist_parser decllist tokenlist = 
	match decl_parser tokenlist with
  | Success decls, [] -> Success (List.rev (decls::decllist))
  | Success decls, list -> decllist_parser (decls::decllist) list
  | Error e, list -> Error (e^"\n"^token_list_to_string list)

let rec typedecllist_parser typedecllist = function
	| (_,TYPE)::(_,IDtok id)::(l1,EQ)::list ->
		(match typedecl_parser id list with
		| Success typedecl, (_,SEMICOLON)::list -> typedecllist_parser (typedecl::typedecllist) list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No semicolon, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after id." l1), []
		| Error e, list -> Error e, list)
	| list -> Success typedecllist, list

(* SPL = Decl+ *)
let parser decllist tokenlist = 
	match remove_comments tokenlist with
	| Error e -> Error e
	| Success tokenlist ->
		(match typedecllist_parser [] tokenlist with
		| Error e, tokenlist -> Error e
		| Success typedecllist,tokenlist -> 
			(match decllist_parser [] tokenlist with
			| Error e -> Error e
			| Success decllist -> Success (typedecllist,decllist)));;
  	
