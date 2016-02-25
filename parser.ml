open Types
open Tokenizer

(* Levert een lijst met gevonden fieldtokens *)
(* Geen fieldtokens = lege lijst             *)
let rec parse_field field_list = function
	| PERIOD::(Fieldtoken t)::list -> parse_field (t::field_list) list
	| list -> Field (List.rev field_list);;

let is_op1 c =
	c == ['!'] || c == ['-'];;

let rec exp_parser = function
	| (Inttok i)::list -> Success (Exp_int (Inttoken i)), list
	| (Chartok c)::list -> Success (Exp_char c), list
	| FALSE::list -> Success (Exp_bool false), list
	| TRUE::list -> Success (Exp_bool true), list
	| OPEN_BRACK::CLOSE_BRACK::list -> Success (Exp_emptylist), list
	| (IDtok id)::OPEN_PAR::list -> (match parse_funcall [] list with
			| Success exps, list -> Success (Exp_function_call ((Id id), exps)), list 
			| Error e, list -> Error e, list)
	|	(IDtok id)::list -> Success (Exp_field (Id id, parse_field [] list)), list
	| OPEN_PAR::list -> (match (exp_parser list) with
		| Success exp1, COMMA::list -> (match (exp_parser list) with
			| Success exp2, CLOSE_PAR::list -> Success (Exp_tuple (exp1,exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, CLOSE_PAR::list -> Success (Exp_parentheses exp), list
		| Error e, list -> Error e, list)
	| (Optok c)::list when (is_op1 c) -> (match (exp_parser list) with
		| Success exp, list ->  Success (Exp_prefix ((Op1 (List.hd c)), exp)), list
		| Error e, list -> Error e, list)
and
parse_funcall arg_list = function (* nog geen errors bij lege argumenten *)
	| CLOSE_PAR::list -> Success (List.rev arg_list), list
	| COMMA::list -> parse_funcall arg_list list
	| list -> (match (exp_parser list) with
		| Success exp, list -> parse_funcall (exp::arg_list) list
		| Error e, list -> Error e, list)
(* Nu nog "exp op2 exp" *)

let rec type_parser = function
	| (Basictoken a)::list -> Success (Basictype a),list
	| (IDtok id)::list -> Success (Type_id (Id id)),list
	| OPEN_PAR::list -> (match (type_parser list) with
		| Success type1,(COMMA::list) -> (match (type_parser list) with
			| Success type2,(CLOSE_PAR::list) -> Success (Type_tuple (type1,type2)),list
			| Success _, list -> Error ("Geen sluithaak, maar " ^ token_list_to_string list), list
			| Error e, list -> Error e, list)
		| Success _, list -> Error ("Geen komma, maar " ^ token_list_to_string list), list
		| Error e, list -> Error e, list)
	| OPEN_BRACK::list -> (match (type_parser list) with
		| Success(type1),(CLOSE_BRACK::list) -> Success (Type_list type1),list
		| _,(x::list) -> Error ("Geen sluithaak, maar " ^ token_to_string x), list
		| Error e, list -> Error e, list);;

let rec fargs_parser_till_CLOSE_PAR id_list = function
| CLOSE_PAR::list	-> Success (Fargs (List.rev id_list)),list
| (IDtok id)::CLOSE_PAR::list	-> Success (Fargs (List.rev ((Id id)::id_list))),list
| (IDtok id)::COMMA::list -> fargs_parser_till_CLOSE_PAR ((Id id)::id_list) list
| x::list -> Error ("Geen sluithaak of komma, maar " ^ token_to_string x), list

let rettype_parser list = match list with
	| VOID::list -> Success Type_void, list
	| list -> (match type_parser list with
		| Success type1, list -> Success (Rettype type1), list
		| Error e, list -> Error e, list);;

let rec funtype_parser type_list list = match list with
  | ARROW::list	-> (match rettype_parser list with 
  	| Success rettype, list -> Success (Funtype ((List.rev type_list),rettype)), list
  	| Error e, list -> Error e, list)
  | x -> (match type_parser x with
  	| Success type1, list -> funtype_parser (type1::type_list) list
		| Error e, list -> Error e, list);;

let vardecl_rest_parser typetoken = function
	| IDtok id::EQ::list -> (match exp_parser list with
		| Success exp, SEMICOLON::list -> Success (Vardecl (typetoken, Id id, exp)), list
		| Success _, list -> Error ("Geen semicolon, maar " ^ token_list_to_string list), list 
		| Error e, list -> Error e, list)
	| IDtok id::list -> Error ("Geen =, maar " ^ token_list_to_string list), list
	| list -> Error ("Geen id, maar " ^ token_list_to_string list), list

let vardecl_parser = function
  | VAR::list -> vardecl_rest_parser None list
  | list -> (match type_parser list with
		| Success type1, list -> vardecl_rest_parser (Some type1) list
		| Error e, list -> Error e, list);;

let rec vardecl_list_parser_till_ERROR vardecl_list list = match vardecl_parser list with
| Error e, faillist -> Success (List.rev vardecl_list), list
| Success vardecl, list ->  vardecl_list_parser_till_ERROR  (vardecl::vardecl_list) list;;

let stmt_list_parser_till_CLOSE_ACO stmt_list list = match list with
| CLOSE_ACO::list -> Succes (List.rev stmt_list),list
| IF::OPEN_PAR::list -> 
	match exp_parser list with
	| Error e, faillist -> faillist
	| exp, CLOSE_PAR::OPEN_ACO::list -> 
		match stmt_list_parser [] list with
		| if_stmts, ELSE::list -> 
			match stmt_list_parser with
			| else_stmts, lastlist -> stmt_list_parser (Stmt_if_else ((exp,if_stmts,else_stmts)::stmt_list)), lastlist
		| if_stmts, lastlist -> stmt_list_parser (Stmt_if ((exp,if_stmts)::stmt_list)), lastlist
| WHILE::OPEN_PAR::list ->
	match exp_parser list with
	| exp, CLOSE_PAR::OPEN_ACO::list ->
		match stmt_list_parser [] list with
		| while_stmts, lastlist -> stmt_list_parser(Stmt_while((exp,while_stmts)::stmt_list)), lastlist
| RETURN::SEMICOLON::lastlist -> stmt_list_parser(Stmt_return((None)::stmt_list)), lastlist
| RETURN::list ->
	match exp_parser list with
	| exp, SEMICOLON::lastlist -> stmt_list_parser(Stmt_return((exp)::stmt_list)), lastlist
(*stmt_function_call*)
(*stmt_define*)

(* let fundecl_parser id list = match fargs_parser_till_CLOSE_PAR [] list with                    *)
(* | Error e, faillist -> Error e, faillist                                                       *)
(* | Succes fargs, OPEN_ACO::list ->                                                              *)
(* 	(match vardecl_list_parser_till_ERROR with                                                   *)
(* 	| vardecl_list, list ->                                                                      *)
(* 		(match stmt_list_parser_till_CLOSE_ACO with                                                *)
(* 		| stmt_list, lastlist -> Fundecl (id,fargs,None,vardecl_list,stmt_list)))                  *)
(* | fargs,DDPOINT::list ->                                                                       *)
(* 	 (match funtype_parser list with                                                             *)
(* 	| funtype, OPEN_ACO::list ->                                                                 *)
(* 		 (match vardecl_list_parser with                                                           *)
(* 		| vardecl_list, list ->                                                                    *)
(* 			(match stmt_list_parser with                                                             *)
(* 			| [], x::lastlist -> Error "geen statement, maar " ^ token_list_to_string [x]), lastlist *)
(* 			| stmt_list, lastlist -> Fundecl (id,fargs,Some funtype,vardecl_list,stmt_list))));;     *)

let rec spl_parser decllist tokenlist = 
	let decl_parser tokenlist = match tokenlist with
	| VAR::IDtok id::EQ::list -> vardeclvar_parser ID id list
	| IDtok id::OPEN_PAR::list -> fundecl_parser ID id list
	| _ -> vardecltype_parser list in
match decl_parser tokenlist with
| (Succes decls,[]) -> Succes (SPL (List.rev (decls::decllist)))
| (Succes decls,restlist)  -> spl_parser (decls::decllist) restlist
| Error e, faillist -> Error e;;

let structure = spl_parser [] tokenlist;;

(*chartok moet gemaakt worden*)
(*overal goede errors toevoegen*)
(*overal succes toevoegen*)
(*vardecltype_parser*)