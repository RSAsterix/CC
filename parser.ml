open Types
open Tokenizer

(* Levert een lijst met gevonden fieldtokens *)
(* Geen fieldtokens = lege lijst             *)
let rec parse_field field_list = function
	| PERIOD::(Fieldtoken t)::list -> parse_field (t::field_list) list
	| list -> Field (List.rev field_list), list;;

let is_op1 c =
	c == "!" || c == "-";;

let is_op_or c =
	c == "||";;

let is_op_and c =
	c == "&&";;

let is_op_eq c =
	c == "==" || c == ">=" || c == "<=" || c == "!=" || c == "<" || c == ">";;

let is_op_plus c =
	c == "+" || c == "-";;

let is_op_times c =
	c == "*" || c == "/";;

let rec exp_parser = function
	| list -> 
		(match exp_and list with
    | Success exp1, (Optok c)::list when (is_op_or c) -> 
			(match exp_parser list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| x -> x) (* Return either the same success, or the same error *)
and
exp_and = function
	| list -> 
		(match exp_eq list with
    | Success exp1, (Optok c)::list when (is_op_and c) -> 
			(match exp_and list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| x -> x)
and
exp_eq = function
	| list -> 
		(match exp_plus list with
    | Success exp1, (Optok c)::list when (is_op_eq c) -> 
			(match exp_eq list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| x -> x)
and
exp_plus = function
	| list -> 
		(match exp_times list with
    | Success exp1, (Optok c)::list when (is_op_plus c) -> 
			(match exp_plus list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| x -> x)
and
exp_times = function
	| list -> 
		(match exp_strongest list with
    | Success exp1, (Optok c)::list when (is_op_times c) -> 
			(match exp_times list with
			| Success exp2, list -> Success (Exp_infix (exp1, Op2 c, exp2)), list
			| Error e, list -> Error e, list)
		| x -> x)
and
exp_strongest = function
	| (Inttok i)::list -> Success (Exp_int (Inttoken i)), list
	| (Chartok c)::list -> Success (Exp_char c), list
	| FALSE::list -> Success (Exp_bool false), list
	| TRUE::list -> Success (Exp_bool true), list
	| OPEN_BRACK::CLOSE_BRACK::list -> Success (Exp_emptylist), list
	| (IDtok id)::OPEN_PAR::list -> 
		(match parse_funcall [] list with
		| Success exps, list -> Success (Exp_function_call ((Id id), exps)), list 
		| Error e, list -> Error e, list)
	|	(IDtok id)::list -> 
		(match parse_field [] list with
		|  fieldlist, list -> Success (Exp_field (Id id, fieldlist)), list)
	| OPEN_PAR::list -> 
		(match (exp_parser list) with
		| Success exp1, COMMA::list -> 
			(match (exp_parser list) with
			| Success exp2, CLOSE_PAR::list -> Success (Exp_tuple (exp1,exp2)), list
			| Success _, list -> Error ("(exp_strongest) No closing parenthesis after comma, but: " ^ token_list_to_string list), list
			| Error e, list -> Error e, list)
		| Success exp, CLOSE_PAR::list -> Success exp, list (* Haakjes weglaten in AST*)
		| Success _, list -> Error ("(exp_strongest) No closing parenthesis, but: " ^ token_list_to_string list), list
		| Error e, list -> Error e, list)
	| (Optok c)::list when (is_op1 c) -> 
		(match (exp_parser list) with
		| Success exp, list ->  Success (Exp_prefix ((Op1 c), exp)), list
		| Error e, list -> Error e, list)
	| list -> Error ("Empty expression or unexpected token: " ^ token_list_to_string list), list
and
parse_funcall arg_list = function (* nog geen errors bij lege argumenten *)
	| CLOSE_PAR::list -> Success (List.rev arg_list), list
	| COMMA::list -> parse_funcall arg_list list
	| list -> 
		(match (exp_parser list) with
		| Success exp, list -> parse_funcall (exp::arg_list) list
		| Error e, list -> Error e, list)

let rec type_parser = function
	| (Basictoken a)::list -> Success (Basictype a),list
	| (IDtok id)::list -> Success (Type_id (Id id)),list
	| OPEN_PAR::list -> 
		(match (type_parser list) with
		| Success type1,(COMMA::list) -> 
			(match (type_parser list) with
			| Success type2,(CLOSE_PAR::list) -> Success (Type_tuple (type1,type2)),list
			| Success _, list -> Error ("Geen sluithaak, maar " ^ token_list_to_string list), list
			| Error e, list -> Error e, list)
		| Success _, list -> Error ("Geen komma, maar " ^ token_list_to_string list), list
		| Error e, list -> Error e, list)
	| OPEN_BRACK::list -> 
		(match (type_parser list) with
		| Success(type1),(CLOSE_BRACK::list) -> Success (Type_list type1),list
		| Success type1 ,list -> Error ("Geen rechte sluithaak, maar " ^ token_list_to_string list), list
		| Error e, list -> Error e, list)
	| list -> Error ("Geen type, maar " ^ token_list_to_string list), list;;

let rec fargs_parser_till_CLOSE_PAR id_list = function
  | CLOSE_PAR::list	-> Success (Fargs (List.rev id_list)),list
  | (IDtok id)::CLOSE_PAR::list	-> Success (Fargs (List.rev ((Id id)::id_list))),list
  | (IDtok id)::COMMA::list -> fargs_parser_till_CLOSE_PAR ((Id id)::id_list) list
  | list -> Error ("Geen sluithaak of komma, maar " ^ token_list_to_string list), list;;

let rettype_parser = function
	| VOID::list -> Success Type_void, list
	| list -> 
		(match type_parser list with
		| Success type1, list -> Success (Rettype type1), list
		| Error e, list -> Error e, list);;

let rec funtype_parser type_list = function
  | ARROW::list	-> 
		(match rettype_parser list with 
  	| Success rettype, list -> Success (Funtype ((List.rev type_list),rettype)), list
  	| Error e, list -> Error e, list)
  | list -> 
		(match type_parser list with
  	| Success type1, list -> funtype_parser (type1::type_list) list
		| Error e, list -> Error e, list);;

let vardecl_rest_parser typetoken = function
	| IDtok id::EQ::list -> 
		(match exp_parser list with
		| Success exp, SEMICOLON::list -> Success (Vardecl (typetoken, Id id, exp)), list
		| Success _, list -> Error ("Geen semicolon, maar " ^ token_list_to_string list), list 
		| Error e, list -> Error e, list)
	| IDtok id::list -> Error ("Geen =, maar " ^ token_list_to_string list), list
	| list -> Error ("Geen id, maar " ^ token_list_to_string list), list

let vardecl_parser = function
  | VAR::list -> vardecl_rest_parser None list
  | list -> 
		(match type_parser list with
		| Success type1, list -> vardecl_rest_parser (Some type1) list
		| Error e, list -> Error e, list);;

let rec vardecl_list_parser_till_ERROR vardecl_list list = match vardecl_parser list with
  | Error e, faillist -> Success (List.rev vardecl_list), list
  | Success vardecl, list ->  vardecl_list_parser_till_ERROR  (vardecl::vardecl_list) list;;

let rec stmt_list_parser_till_CLOSE_ACO stmt_list = function
  | CLOSE_ACO::list -> Success (List.rev stmt_list),list
  | list -> 
  	(match stmt_parser list with
  	| Error e, faillist -> Error e, faillist
  	| Success stmt, list -> stmt_list_parser_till_CLOSE_ACO (stmt::stmt_list) list)
and 
stmt_parser = function
  | IF::OPEN_PAR::list -> 
  	(match exp_parser list with
  	| Error e, faillist -> Error e, faillist
  	| Success exp, CLOSE_PAR::OPEN_ACO::list -> 
  		(match stmt_list_parser_till_CLOSE_ACO [] list with
  		| Error e, faillist -> Error e, faillist
  		| Success if_stmts, ELSE::OPEN_ACO::list -> 
  			(match stmt_list_parser_till_CLOSE_ACO [] list with
  			| Error e, faillist -> Error e, faillist
  			| Success else_stmts, lastlist -> Success (Stmt_if_else (exp,if_stmts,else_stmts)), lastlist)
  		| Success if_stmts, lastlist -> Success (Stmt_if (exp,if_stmts)), lastlist)
  	| Success exp, list -> Error ("Geen sluithaakje, maar " ^ token_list_to_string list), list)
  | WHILE::OPEN_PAR::list ->
  	(match exp_parser list with
  	| Error e, faillist -> Error e, faillist
  	| Success exp, CLOSE_PAR::OPEN_ACO::list ->
  		(match stmt_list_parser_till_CLOSE_ACO [] list with
  		| Error e, faillist -> Error e, faillist
  		| Success while_stmts, lastlist -> Success (Stmt_while(exp,while_stmts)), lastlist)
  	| Success exp, list -> Error ("Geen sluithaakje, maar " ^ token_list_to_string list), list)
  | RETURN::SEMICOLON::lastlist -> Success (Stmt_return(None)), lastlist
  | RETURN::list ->
  	(match exp_parser list with
  	| Error e, faillist -> Error e, faillist
  	| Success exp, SEMICOLON::lastlist -> Success (Stmt_return(Some(exp))), lastlist
		| Success exp, list -> Error ("Geen semicolon, maar " ^ token_list_to_string list), list)
  | (IDtok id)::OPEN_PAR::list -> 
  	(match parse_funcall [] list with
  	| Error e, faillist -> Error e, faillist
  	| Success exp_list, lastlist -> Success (Stmt_function_call(Id id,exp_list)), lastlist)
  | (IDtok id)::list ->
		(match parse_field [] list with
		| fieldlist, EQ::list -> 
    	(match exp_parser list with
    	| Error e, faillist -> Error e, faillist
    	| Success exp, SEMICOLON::lastlist -> Success (Stmt_define (Id id,fieldlist,exp)), lastlist
    	| Success exp, lastlist -> Error ("Geen semicolon, maar " ^ token_list_to_string list), list)
		| fieldlist, list -> Error ("Geen =-teken, maar " ^ token_list_to_string list), list)
  | list -> Error ("Geen statement, maar " ^ token_list_to_string list), list;;


let fundecl_parser id list = match fargs_parser_till_CLOSE_PAR [] list with
  | Error e, faillist -> Error e, faillist
  | Success fargs, OPEN_ACO::list ->
  	(match vardecl_list_parser_till_ERROR [] list with
		| Error e, faillist -> Error e, faillist
  	| Success vardecl_list, list ->
  		(match stmt_list_parser_till_CLOSE_ACO [] list with
  		| Error e, faillist -> Error e, faillist
  		| Success [], lastlist -> Error ("geen statement, maar " ^ token_list_to_string lastlist), lastlist
  		| Success stmt_list, lastlist -> Success (Fundecl (id,fargs,None,vardecl_list,stmt_list)),lastlist))
  | Success fargs,DDPOINT::list ->
    (match funtype_parser [] list with
    | Error e, faillist -> Error e, faillist
    | Success funtype, OPEN_ACO::list ->
      (match vardecl_list_parser_till_ERROR [] list with
			| Error e, faillist -> Error e, faillist
      | Success vardecl_list, list ->
        (match stmt_list_parser_till_CLOSE_ACO [] list with
        | Error e, faillist -> Error e, faillist
        | Success [], lastlist -> Error ("geen statement, maar " ^ token_list_to_string lastlist), lastlist
        | Success stmt_list, lastlist -> Success (Fundecl (id,fargs,Some funtype,vardecl_list,stmt_list)),lastlist))
		|Success funtype, list -> Error ("geen openhaakje, maar " ^ token_list_to_string list), list)
	| Success fargs, list -> Error ("geen openhaakje of ::, maar " ^ token_list_to_string list), list;;

let decl_parser = function
	| IDtok id::OPEN_PAR::list ->
		(match fundecl_parser (Id id) list with
		| Success fundecl, list -> Success (Decl_fun fundecl), list
		| Error e, faillist -> Error e, faillist)
	| list -> 
		(match vardecl_parser list with
		| Success vardecl, list -> Success (Decl_var vardecl), list
		| Error e, faillist -> Error e, faillist);;

let rec spl_parser decllist tokenlist = 
	match decl_parser tokenlist with
  | Success decls,[] -> Success (SPL (List.rev (decls::decllist)))
  | Success decls,restlist  -> spl_parser (decls::decllist) restlist
  | Error e, faillist -> Error e;;

(*overal goede errors toevoegen*)
(*overal success toevoegen*)