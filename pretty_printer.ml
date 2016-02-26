open Types
open Char_func

let print_id = function
	| Id id -> print_string (implode id);;

let print_int = function
	| Inttoken [] -> ()
	| Inttoken i -> print_string (implode i);;

let print_op1 = function
	| Op1 o -> print_string o;;

let print_op2 = function
	| Op2 o -> print_string o;;

let rec print_fields = function
	| Field [] -> ();
	| Field (Hd::field_list) -> print_string ".hd"; print_fields (Field field_list);
	| Field (Tl::field_list) -> print_string ".tl"; print_fields (Field field_list);
	| Field (Fst::field_list) -> print_string ".fst"; print_fields (Field field_list);
	| Field (Snd::field_list) -> print_string ".snd"; print_fields (Field field_list);;
		 
let rec print_stmt_list = function
	| [] -> ();
	| stmt::list -> print_stmt stmt; print_stmt_list list;
and
print_stmt = function
	| Stmt_if (exp, stmt_list) -> 
		print_string "if(";
		print_exp exp;
		print_string"){";
		print_stmt_list stmt_list;
		print_string"}"
	| Stmt_if_else (exp, stmt_list1, stmt_list2) -> 
		print_string "if(";
		print_exp exp;
		print_string"){";
		print_stmt_list stmt_list1;
		print_string"}else{";
		print_stmt_list stmt_list2;
		print_string"}"
	| Stmt_while (exp, stmt_list) ->
		print_string "while(";
		print_exp exp;
		print_string"){";
		print_stmt_list stmt_list;
		print_string"}"
	| Stmt_define (id, fields, exp) ->
		print_id id;
		print_fields fields;
		print_string "=";
		print_exp exp;
		print_string ";";
	| Stmt_function_call (id, exp_list) ->
		print_id id;
		print_string "(";
		print_exp_list exp_list;
		print_string ")";
	| Stmt_return None ->
		print_string "return;"
	| Stmt_return (Some exp) ->
		print_exp exp;
		print_string ";";
and
print_exp = function
	| Exp_field (id, fields) ->
		print_id id;
		print_fields fields;
	| Exp_infix (exp1, op2, exp2) ->
		print_exp exp1;
		print_op2 op2;
		print_exp exp2;
and
print_exp_list = function
	| [] -> ();
	| exp::exp_list -> print_exp exp; print_exp_list exp_list;;