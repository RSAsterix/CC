open Parser

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
				| Error e, list -> []) (* Hoe gaan we dit oplossen? *)
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