open Types
open Tokenizer

(* Levert een lijst met gevonden fieldtokens *)
(* Geen fieldtokens = lege lijst             *)
let rec parse_field field_list = function
	| PERIOD::(Fieldtoken t)::list -> parse_field (t::field_list) list
	| list -> Field (List.rev field_list);;

let is_op1 c =
	c == '!' || c == '-';;

let rec parse_exp = function
	| (Inttok i)::list -> Success (Exp_int (Inttoken i)), list
	| (Chartok c)::list -> Success (Exp_char c), list
	| FALSE::list -> Success (Exp_bool false), list
	| TRUE::list -> Success (Exp_bool true), list
	| OPEN_BRACK::CLOSE_BRACK::list -> Success (Exp_emptylist), list
	| (IDtok id)::list -> (match list with
		| OPEN_PAR::list -> (let rec parse_funcall arg_list = function
			| CLOSE_PAR::list -> (List.rev arg_list), list
			| COMMA::list -> parse_funcall arg_list list
			| list -> (match (parse_exp list) with
				| Success exp, list -> parse_funcall (exp::arg_list) list
				| Error e, list -> [], list) (* Hoe gaan we dit oplossen? *)
			in Success (Exp_function_call ((Id id), (parse_funcall [] list))), list) 
		|	list -> Success (Exp_field (Id id, parse_field [] list)), list)
	| OPEN_PAR::list -> (match (parse_exp list) with
		| Success exp1, COMMA::list -> (match (parse_exp list) with
			| Success exp2, CLOSE_PAR::list -> Success (Exp_tuple (exp1,exp2)), list
			| Error e, list -> Error e, list)
		| Success exp, CLOSE_PAR::list -> Success (Exp_parentheses exp), list
		| Error e, list -> Error e, list)
	| (Optok c)::list when (is_op1 c) -> (match (parse_exp list) with
		| Success exp, list ->  Success (Exp_prefix ((Op1 c), exp)), list
		| Error e, list -> Error e, list)
(* Nu nog "exp op2 exp" *)


let rec exp_parser list = 
  let rec basicexp_parser list = match list with
  | IDtok id::Fieldtoken field::list -> (Exp_field (Id id,Field [field]),list) (*fixen dat het meerdere fieldtokens kan hebben*)
  | Optok ['-']::Inttok int::list -> (Exp_int (Inttoken ('-'::int)), list)
  | Inttok int::list -> (Exp_int (Inttoken int), list)
  | Optok [op1]::list when op1 == '!' || op1 == '-' -> (match basicexp_parser list with
  	| (exp, list) -> (Exp_prefix (Op1 op1, exp), list))
  | (IDtok [c])::list -> (Exp_char c, list)
  | FALSE::list -> (Exp_bool false, list)
  | TRUE::list -> (Exp_bool true, list)
  | EMPTYLIST::list -> (Exp_emptylist, list) in
match list with
| IDtok id::OPEN_PAR::CLOSE_PAR::list -> (Exp_function_call (Id id,[]),list)
| IDtok id::OPEN_PAR::list -> (match exp_parser list with
	| (exp,CLOSE_PAR::list) -> (Exp_function_call (Id id,[exp]),list)
	| (exp,COMMA::list) -> (match exp_parser (IDtok id::OPEN_PAR::list) with
		| (Exp_function_call(id,explist),newlist) -> (Exp_function_call(id,exp::explist),newlist)))
| OPEN_PAR::list -> (match exp_parser list with
	| (exp,CLOSE_PAR::list) -> (Exp_parentheses exp, list)
	| (exp1,COMMA::list1) -> (match exp_parser list1 with
		| (exp2,CLOSE_PAR::list2) -> (Exp_tuple(exp1,exp2),list)))
| _ -> (match basicexp_parser list with
	|  (exp1,Optok op2::list) -> (match exp_parser list with
		| (exp2,list) -> (Exp_infix (exp1,Op2 op2,exp2),list))
	| x -> x);;

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

let vardeclvar_parser id list = match exp_parser list with
| (exp,SEMICOLON::restlist) -> (Decl_var (Vardecl_var (id, exp)) ,restlist);;

let rec fargs_parser id_list = function
| CLOSE_PAR::list	-> (Fargs (List.rev id_list)),list
| (IDtok id)::list -> fargs_parser ((Id id)::id_list) list;;

let funtype_parser type_list list = match list with
| ARROW::list	-> (match rettype_parser with 
	| rettype, list -> (Funtype ((List.rev type_list),rettype)),list)
| x -> (match type_parser x with (type1, list) -> funtype_parser (type1::type_list) list);;

let vardecl_parser list = match list with
| VAR::IDtok id::EQ::list -> vardeclvar_parser id list
| _ ->  vardecltype_parser list;;

let vardecl_list_parser vardecl_list list = match vardecl_parser list with
| Error e, faillist -> (List.rev vardecl_list),list
| Succes vardecl, list ->  vardecl_list_parser  (vardecl::vardecl_list) list;;

let stmt_list_parser stmt_list list = match list with
| CLOSE_ACO::list -> (List.rev stmt_list),list
| IF::OPEN_PAR::list -> 
	match exp_parser list with
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

(* let fundecl_parser id list = match fargs_parser [] list with                                   *)
(* | fargs, OPEN_ACO::list ->                                                                     *)
(* 	(match vardecl_list_parser with                                                              *)
(* 	| vardecl_list, list ->                                                                      *)
(* 		(match stmt_list_parser with                                                               *)
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
| (decls,[]) -> List.rev (decls::decllist)
| (decls,restlist)  -> spl_parser (decls::decllist) restlist;;


let structure = SPL (spl_parser [] tokenlist);;

(*chartok moet gemaakt worden*)
(*overal goede errors toevoegen*)
(*overal succes toevoegen*)