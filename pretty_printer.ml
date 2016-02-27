open Types
open Char_func
open Format

let print_bool = function
	| true -> 
		print_string "True";
	| false -> 
		print_string "False";;

let print_id = function
	| Id id -> 
		print_string (implode id);;

let print_inttoken = function
	| Inttoken [] -> ();
	| Inttoken i -> 
		print_string (implode i);;

let print_op1 = function
	| Op1 o -> 
		print_string o;;

let print_op2 = function
	| Op2 o -> 
		print_string o;;

let rec print_fields = function
	| Field [] -> ();
	| Field (Hd::ls) -> 
		print_string ".hd";
		print_fields (Field ls);
	| Field (Tl::ls) -> 
		print_string ".tl"; 
		print_fields (Field ls);
	| Field (Fst::ls) -> 
		print_string ".fst"; 
		print_fields (Field ls);
	| Field (Snd::ls) -> 
		print_string ".snd"; 
		print_fields (Field ls);;

let rec print_exp = function
	| Exp_field (id, flds) ->
		print_id id;
		print_fields flds;
	| Exp_infix (exp1, op2, exp2) -> (* associativiteit met haakjes? *)
		print_exp exp1;
		print_string " ";
		print_op2 op2;
		print_string " ";
		print_exp exp2;
	| Exp_prefix (op1, exp) ->
		print_op1 op1;
		print_exp exp;
	| Exp_int int ->
		print_inttoken int;
	| Exp_char c ->
		print_string "'";
		print_char c;
		print_string "'";
	| Exp_bool b ->
		print_bool b;
	| Exp_function_call (id, exps) ->
		print_funcall (id, exps);
	| Exp_emptylist ->
		print_string "[]"
	| Exp_tuple (exp1, exp2) ->
		print_string "(";
		print_exp exp1;
		print_string ",";
		print_exp exp2;
		print_string ")";
and print_exp_list = function
	| [] -> ();
	| [exp] ->
		print_exp exp;
	| exp::exp_list ->
		print_exp exp;
		print_string ", ";
		print_exp_list exp_list;
and print_stmt = function
	| Stmt_if (exp, stmt_list) -> 
		print_string "if(";
		print_exp exp;
		print_string "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list;
		close_box ();
		print_cut();
		print_string "}";
	| Stmt_if_else (exp, stmt_list1, stmt_list2) -> 
		print_string "if(";
		print_exp exp;
		print_string "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list1;
		close_box ();
		print_cut ();
		print_string "}else{";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list2;
		close_box ();
		print_cut ();
		print_string "}";
	| Stmt_while (exp, stmt_list) ->
		print_string "while(";
		print_exp exp;
		print_string "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list;
		close_box ();
		print_cut ();
		print_string "}";
	| Stmt_define (id, fields, exp) ->
		print_id id;
		print_fields fields;
		print_string " = ";
		print_exp exp;
		print_string ";";
	| Stmt_function_call (id, exps) ->
		print_funcall (id, exps);
		print_string ";";
	| Stmt_return x ->
		print_string "return ";
		print_exp_option x;
		print_string ";";
and print_stmt_list = function
	| [] -> ();
	| [stmt] ->
		print_stmt stmt;
	| stmt::ls ->
		print_stmt stmt;
		print_cut ();
		print_stmt_list ls;
and print_exp_option = function
	| None -> ();
	| Some exp ->
		print_exp exp;
and print_funcall = function
	| (id, exps) ->
		print_id id;
		print_string "(";
		print_exp_list exps;
		print_string ")";;

let rec print_fargs = function
	| Fargs [] -> ()
	| Fargs [a] ->
		print_id a;
	| Fargs (a::list) ->
		print_id a;
		print_string ", ";
		print_fargs (Fargs list);;

let print_basictype = function
	| Type_int -> print_string "Int";
	| Type_bool -> print_string "Bool";
	| Type_char -> print_string "Char";;

let rec print_typetoken = function
	| Basictype b -> print_basictype b;
	| Type_tuple (t1, t2) ->
		print_string "(";
		print_typetoken t1;
		print_string ", ";
		print_typetoken t2;
		print_string ")";
	| Type_list t ->
		print_string "[";
		print_typetoken t;
		print_string "]";
	| Type_id id ->
		print_id id;;

let print_rettype = function
	| Type_void ->
		print_string "Void";
	| Rettype t ->
		print_typetoken t;;

let rec print_funtype = function
	| Funtype ([], ret) ->
		print_string "-> ";
		print_rettype ret;
		print_string " ";
	| Funtype (a::list, ret) ->
		print_typetoken a;
		print_string " ";
		print_funtype (Funtype (list, ret));;

let print_var_option = function
	| None ->
		print_string "var";
	| Some t ->
		print_typetoken t;;

let rec print_vardecl = function
	| Vardecl (t, id, exp) ->
		print_var_option t;
		print_string " ";
		print_id id;
		print_string " = ";
		print_exp exp;
		print_string ";";;

let rec print_vardecl_list = function
	| [] -> ();
	| x::list -> 
		print_vardecl x;
		print_cut ();
		print_vardecl_list list;;

let print_funtype_option = function
	| None -> ();
	| Some ft ->
		print_string " :: ";
		print_funtype ft;;

let rec print_fundecl = function
	| Fundecl (id, fargs, funtype, vardecl_list, stmt_list) ->
		print_id id;
		print_string "(";
		print_fargs fargs;
		print_string ")";
		print_funtype_option funtype;
		print_string "{";
		print_break 0 2;
		open_vbox 0;
		print_vardecl_list vardecl_list;
		print_stmt_list stmt_list;
		close_box ();
		print_cut ();
		print_string "}";;

let print_decl = function
	| Decl_var v -> 
		print_vardecl v;
	| Decl_fun f ->
		print_fundecl f;;

let rec print_spl = function
	| SPL [] -> ();
	| SPL (x::list) ->
		open_vbox 0;
		print_decl x;
		close_box ();
		print_cut ();
		print_spl (SPL list);;
		
		