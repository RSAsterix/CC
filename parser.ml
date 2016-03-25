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
	| (_,Basictoken a)::list -> Success (Basictype a),list
	| (_,IDtok id)::list -> Success (Type_id (Id id)),list
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
	| (l,x)::list -> Error (sprintf "(r.%i) Unexpected token: %s" l (token_to_string x)), (l,x)::list
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
  	| Success rettype, list -> Success (Funtype ((List.rev type_list), rettype)), list
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
		| Success exp, (_,SEMICOLON)::list -> Success (Vardecl (typetoken, Id id, exp)), list
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
stmt_parser = function
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
	| (_,IDtok id)::(_,OPEN_PAR)::list -> 
  	(match funcall_parser list with
  	| Success exp_list, list -> Success (Stmt_function_call (Id id, exp_list)), list
		| Error e, list -> Error e, list)
	| (l0,IDtok id)::list ->
		(match (field_parser [] list) with
		| Success fieldlist, (l1,EQ)::list ->
			(let rec packer = function
				| [] -> (Nofield (Id id))
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
	| (l,x)::list -> Error (sprintf "(r.%i) Unexpected token: %s" l (token_to_string x)), (l,x)::list
	| [] -> Error "Unexpected EOF while parsing statement.", []

(* fargs =   ')' | fargs2          *)
(* fargs2 = id ')' | id ',' fargs2 *)
(*opgesplitst in twee functies, zodat fargs ook '()' mag zijn*)
let fargs_parser list =
	let rec fargs2_parser id_list = function
		| (_,IDtok id)::(_,CLOSE_PAR)::list	-> Success (Fargs (List.rev ((Id id)::id_list))),list
  	| (_,IDtok id)::(_,COMMA)::list -> fargs2_parser ((Id id)::id_list) list
		| (_,IDtok id)::(l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis or comma, but: %s" l (token_to_string x)), (l,x)::list
		| (l,x)::list -> Error (sprintf "(r.%i) No id, but: %s" l (token_to_string x)), (l,x)::list
		| [] -> Error "Unexpected EOF when parsing function arguments.", []
  in match list with
	| (_,CLOSE_PAR)::list -> Success (Fargs []), list
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
  		| Success stmt_list, list -> Success (Fundecl (id, fargs, None, vardecl_list, stmt_list)), list))
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
        | Success stmt_list, list -> Success (Fundecl (id, fargs, Some funtype, vardecl_list, stmt_list)), list))
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No opening acolade, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after parsing '::'." l0), [])
	| Success _, (l,x)::list -> Error (sprintf "(r.%i) No opening parenthesis or '::', but: %s" l (token_to_string x)), (l,x)::list
	| Success _, [] -> Error "Unexpected EOF while parsing function declaration.", [];;

(* Decl = id '('  FunDecl | VarDecl *)
let decl_parser = function
	| (_,IDtok id)::(_,OPEN_PAR)::list ->
		(match fundecl_parser (Id id) list with
		| Success fundecl, list -> Success (Decl_fun fundecl), list
		| Error e, faillist -> Error e, faillist)
	| (l,IDtok id)::[] -> Error (sprintf "(r.%i) Unexpected EOF after parsing id.\nBy the way: is '%s' a type for a variable, or a function name without arguments?" l id), []
	| list -> 
		(match vardecl_parser list with
		| Success vardecl, list -> Success (Decl_var vardecl), list
		| Error e, faillist -> Error e, faillist);;

(* SPL = Decl+ *)
let rec spl_parser decllist tokenlist = 
	match decl_parser tokenlist with
  | Success decls, [] -> Success (SPL (List.rev (decls::decllist)))
  | Success decls, list -> spl_parser (decls::decllist) list
  | Error e, list -> Error e;;