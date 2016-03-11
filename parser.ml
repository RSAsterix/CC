open Types
open Tokenizer
open Char_func

(* field = '.' fieldtoken [field] *)
(* fieldtoken = 'hd' | 'tl' | 'fst' | 'snd' *)
let rec field_parser field_list = function
	| (_,PERIOD)::(_,Fieldtoken t)::list -> field_parser (t::field_list) list
	| (l,PERIOD)::list -> Error ("(r." ^ string_of_int l ^ ") No field, but: " ^ token_list_to_string list), list
	| list -> Success (Field (List.rev field_list)), list;;

(* exp = expLogical [opColon exp]             *)
let rec exp_parser = function
	| list -> 
		(match exp_logical list with
    | Success exp1, (_,Optok c)::list when (is_op_colon c) -> 
			(match exp_parser list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, list -> Success exp, list
		| Error e, list -> Error e, list)
and
(* expLogical = expEq [opLogical expLogical]  *)
exp_logical = function
	| list -> 
		(match exp_eq list with
    | Success exp1, (_,Optok c)::list when (is_op_logical c) -> 
			(match exp_logical list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, list -> Success exp, list
		| Error e, list -> Error e, list)
and
(* expEq = expPlus [opEq expEq]               *)
exp_eq = function
	| list -> 
		(match exp_plus list with
    | Success exp1, (_,Optok c)::list when (is_op_eq c) -> 
			(match exp_eq list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, list -> Success exp, list
		| Error e, list -> Error e, list)
and
(* expPlus = expTimes [opPlus expPlus]        *)
exp_plus = function
	| list -> 
		(match exp_times list with
    | Success exp1, (_,Optok c)::list when (is_op_plus c) -> 
			(match exp_plus list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, list -> Success exp, list
		| Error e, list -> Error e, list)
and
(* expTimes = expStrongest [opTimes expTimes] *)
exp_times = function
	| list -> 
		(match exp_strongest list with
    | Success exp1, (_,Optok c)::list when (is_op_times c) -> 
			(match exp_times list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, list -> Success exp, list
		| Error e, list -> Error e, list)
and
(* expStrongest =	int                 *)
(* 							| char                *)
(* 							| 'False'             *)
(* 							| 'True'              *)
(* 							| '[]'                *)
(* 							| id funcall          *)
(* 							| id field            *)
(* 							| '(' exp ',' exp ')' *)
(* 							| '(' exp ')'         *)
(* 							| op1 exp             *)
exp_strongest = function
	| (_,Inttok i)::list -> Success (Exp_int (Inttoken i)), list
	| (_,Chartok c)::list -> Success (Exp_char c), list
	| (_,FALSE)::list -> Success (Exp_bool false), list
	| (_,TRUE)::list -> Success (Exp_bool true), list
	| (_,EMPTYLIST)::list -> Success (Exp_emptylist), list
	| (_,IDtok id)::(_,OPEN_PAR)::list -> 
		(match funcall_parser list with
		| Success exps, list -> Success (Exp_function_call ((Id id), exps)), list 
		| Error e, list -> Error e, list)
	|	(_,IDtok id)::list -> 
		(match field_parser [] list with
		| Success fieldlist, list -> Success (Exp_field (Id id, fieldlist)), list
		| Error e, list -> Error e, list)
	| (_,OPEN_PAR)::list -> 
		(match (exp_parser list) with
		| Success exp1, (l0,COMMA)::list -> 
			(match (exp_parser list) with
			| Success exp2, (_,CLOSE_PAR)::list -> Success (Exp_tuple (exp1,exp2)), list
			| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis after comma, but: " ^ token_to_string x), (l,x)::list
			| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after comma."), []
			| Error e, list -> Error e, list)
		| Success exp, (_,CLOSE_PAR)::list -> Success exp, list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis, but: " ^ token_to_string x), (l,x)::list
		| Error e, list -> Error e, list)
	| (_,Optok c)::list when (is_op1 c) -> 
		(match (exp_parser list) with
		| Success exp, list ->  Success (Exp_prefix ((Op1 c), exp)), list
		| Error e, list -> Error e, list)
	| (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") Empty expression or unexpected token: " ^ token_to_string x), (l,x)::list
	| [] -> Error "Unexpected EOF while parsing expression.", []
and
(* funcall = ')' | actargs *)
funcall_parser list =
	(* actargs = exp ')' | exp ',' actargs *)
	let rec actargs_parser arg_list list = (match (exp_parser list) with
		| Success exp, (_,CLOSE_PAR)::list -> Success (List.rev (exp::arg_list)), list
		| Success exp, (_,COMMA)::list -> actargs_parser (exp::arg_list) list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis or comma, but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error "Unexpected EOF while parsing function arguments.", []
		| Error e, list -> Error e, list) in
	match list with
	| (_,CLOSE_PAR)::list -> Success([]), list
	| list -> actargs_parser [] list;;

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
			| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis, but: " ^ token_to_string x), (l,x)::list
			| Success _, [] -> Error ("(r." ^ string_of_int l1 ^ ") Unexpected EOF after comma."), []
			| Error e, list -> Error e, list)
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis, but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after comma."), []
		| Error e, list -> Error e, list)
	| (l0,OPEN_BRACK)::list -> 
		(match (type_parser list) with
		| Success type1, (_,CLOSE_BRACK)::list -> Success (Type_list type1), list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing bracket, but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after opening bracket."), [] 
		| Error e, list -> Error e, list)
	| (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") Unexpected token: " ^ token_to_string x), (l,x)::list
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
let vardecl_rest_parser typetoken = function
	| (_,IDtok id)::(l0,EQ)::list -> 
		(match exp_parser list with
		| Success exp, (_,SEMICOLON)::list -> Success (Vardecl (typetoken, Id id, exp)), list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No semicolon, but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after =."), []   
		| Error e, list -> Error e, list)
	| (_,IDtok id)::(l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No =, but " ^ token_to_string x), (l,x)::list
	| (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No id, but " ^ token_to_string x), (l,x)::list
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
			| Success _, (_,ELSE)::(l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No opening acolade, but " ^ token_to_string x), (l,x)::list
			| Success stmt_list1, list -> Success (Stmt_if (exp, stmt_list1)), list
			| Error e, list -> Error e, list)
		| Success _, (_,CLOSE_PAR)::(l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No opening acolade, but " ^ token_to_string x), (l,x)::list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis, but " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after opening parenthesis."), []
		| Error e, list -> Error e, list)
	| (_,WHILE)::(l0,OPEN_PAR)::list ->
		(match exp_parser list with
		| Success exp, (_,CLOSE_PAR)::(_,OPEN_ACO)::list ->
			(match stmt_list_parser [] list with
			| Success stmt_list, list -> Success (Stmt_while (exp, stmt_list)), list
			| Error e, list -> Error e, list)
		| Success _, (_,CLOSE_PAR)::(l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No opening acolade, but " ^ token_to_string x), (l,x)::list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis, but " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after opening parenthesis."), [] 
		| Error e, list -> Error e, list)
	| (_,RETURN)::(_,SEMICOLON)::list -> Success (Stmt_return(None)), list
	| (l0,RETURN)::list ->
		(match exp_parser list with
		| Success exp, (_,SEMICOLON)::list -> Success (Stmt_return(Some(exp))), list
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No semicolon, but: " ^ token_to_string x), list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after parsing 'return'."), [] 
		| Error e, list -> Error e, list)
	| (_,IDtok id)::(_,OPEN_PAR)::list -> 
  	(match funcall_parser list with
  	| Success exp_list, list -> Success (Stmt_function_call (Id id, exp_list)), list
		| Error e, list -> Error e, list)
	| (l0,IDtok id)::list ->
		(match (field_parser [] list) with
		| Success fieldlist, (l1,EQ)::list -> 
    	(match exp_parser list with
    	| Success exp, (_,SEMICOLON)::list -> Success (Stmt_define (Id id, fieldlist, exp)), list
    	| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No semicolon, but: " ^ token_to_string x), (l,x)::list
			| Success _, [] -> Error ("(r." ^ string_of_int l1 ^ ") Unexpected EOF after parsing '='."), []   
			| Error e, list -> Error e, list)
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No '=', but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after parsing " ^ id ^ "."), [] 
		| Error e, list -> Error e, list)
	| (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") Unexpected token: " ^ token_to_string x), list
	| [] -> Error ("Unexpected EOF while parsing statement."), []

(* fargs =   ')' | fargs2          *)
(* fargs2 = id ')' | id ',' fargs2 *)
(*opgesplitst in twee functies, zodat fargs ook '()' mag zijn*)
let fargs_parser list =
	let rec fargs2_parser id_list = function
		| (_,IDtok id)::(_,CLOSE_PAR)::list	-> Success (Fargs (List.rev ((Id id)::id_list))),list
  	| (_,IDtok id)::(_,COMMA)::list -> fargs2_parser ((Id id)::id_list) list 
		| (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No closing parenthesis or comma, but: " ^ token_to_string x), (l,x)::list
		| [] -> Error ("Unexpected EOF when parsing function arguments."), []
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
			| Error e, (l,VAR)::list -> Error ("(r." ^ string_of_int l ^ ") Previous variable decleration parse failed, with error:\n" ^ e), list
  		| Error e, list -> Error e, list
  		| Success [], (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") Not the beginning of a statement, but: " ^ token_to_string x), (l,x)::list
			| Success [], [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after parsing opening acolade."), [] 
  		| Success stmt_list, list -> Success (Fundecl (id, fargs, None, vardecl_list, stmt_list)), list))
  | Success fargs, (l0,DDPOINT)::list ->
    (match funtype_parser [] list with
    | Error e, list -> Error e, list
    | Success funtype, (l1,OPEN_ACO)::list ->
      (match vardecl_list_parser [] list with
			| Error e, list -> Error e, list
      | Success vardecl_list, list ->
        (match stmt_list_parser [] list with
				| Error e, (l,VAR)::list -> Error ("(r." ^ string_of_int l ^ ") Previous variable declaration parse failed, with error:\n" ^ e), list
        | Error e, list -> Error e, list
        | Success [], (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No statement, but: " ^ token_to_string x), (l,x)::list
				| Success [], [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after parsing opening acolade."), [] 
        | Success stmt_list, list -> Success (Fundecl (id, fargs, Some funtype, vardecl_list, stmt_list)), list))
		| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No opening acolade, but: " ^ token_to_string x), (l,x)::list
		| Success _, [] -> Error ("(r." ^ string_of_int l0 ^ ") Unexpected EOF after parsing '::'."), [])
	| Success _, (l,x)::list -> Error ("(r." ^ string_of_int l ^ ") No opening parenthesis or ::, but: " ^ token_to_string x), (l,x)::list
	| Success _, [] -> Error ("Unexpected EOF while parsing function declaration."), [];;

(* Decl = id '('  FunDecl | VarDecl *)
let decl_parser = function
	| (_,IDtok id)::(_,OPEN_PAR)::list ->
		(match fundecl_parser (Id id) list with
		| Success fundecl, list -> Success (Decl_fun fundecl), list
		| Error e, faillist -> Error e, faillist)
	| list -> 
		(match vardecl_parser list with
		| Success vardecl, list -> Success (Decl_var vardecl), list
		| Error e, faillist -> Error e, faillist);;

(* SPL = Decl+ *)
let rec spl_parser decllist tokenlist = 
	match decl_parser tokenlist with
  | Success decls,[] -> Success (SPL (List.rev (decls::decllist)))
  | Success decls,restlist  -> spl_parser (decls::decllist) restlist
  | Error e, faillist -> Error e;;