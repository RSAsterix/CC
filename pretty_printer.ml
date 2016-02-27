open Types
open Char_func
open Format

let shout = print_string;;

let print_bool = function
	| true -> shout "True";
	| false -> shout "False";;

let print_id = function
	| Id id -> shout id;;

let print_inttoken = function
	| Inttoken i -> print_int i;;

let print_op1 = function
	| Op1 o -> shout o;;

let print_op2 = function
	| Op2 o -> shout o;;

let rec print_fields = function
	| Field [] -> ();
	| Field (Hd::ls) -> 
		shout ".hd";
		print_fields (Field ls);
	| Field (Tl::ls) -> 
		shout ".tl"; 
		print_fields (Field ls);
	| Field (Fst::ls) -> 
		shout ".fst"; 
		print_fields (Field ls);
	| Field (Snd::ls) -> 
		shout ".snd"; 
		print_fields (Field ls);;

(* Is op1 zwakker dan op2? *)
let weaker (Op2 op1) (Op2 op2) = true;; (* deze moet nog *)

let rec isLower exp op = 	match exp with
	| Exp_infix (e1, o, e2) -> (weaker o op);
	| e -> false;;

let rec print_exp = function
	| Exp_field (id, flds) ->
		print_id id;
		print_fields flds;
	| Exp_infix (exp1, op2, exp2) -> (* associativiteit met haakjes? *)
		(if (isLower exp1 op2) then (shout "("; print_exp exp1; shout ")";)else(print_exp exp1;));	
		shout " ";
		print_op2 op2;
		shout " ";
		(if (isLower exp2 op2) then (shout "("; print_exp exp2; shout ")";)else(print_exp exp2;));
	| Exp_prefix (op1, exp) ->
		print_op1 op1;
		print_exp exp;
	| Exp_int int ->
		print_inttoken int;
	| Exp_char c ->
		shout "'";
		print_char c;
		shout "'";
	| Exp_bool b ->
		print_bool b;
	| Exp_function_call (id, exps) ->
		print_funcall (id, exps);
	| Exp_emptylist ->
		shout "[]"
	| Exp_tuple (exp1, exp2) ->
		shout "(";
		print_exp exp1;
		shout ",";
		print_exp exp2;
		shout ")";
and print_exp_list = function
	| [] -> ();
	| [exp] ->
		print_exp exp;
	| exp::exp_list ->
		print_exp exp;
		shout ", ";
		print_exp_list exp_list;
and print_stmt = function
	| Stmt_if (exp, stmt_list) -> 
		shout "if(";
		print_exp exp;
		shout "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list;
		close_box ();
		print_cut();
		shout "}";
	| Stmt_if_else (exp, stmt_list1, stmt_list2) -> 
		shout "if(";
		print_exp exp;
		shout "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list1;
		close_box ();
		print_cut ();
		shout "}else{";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list2;
		close_box ();
		print_cut ();
		shout "}";
	| Stmt_while (exp, stmt_list) ->
		shout "while(";
		print_exp exp;
		shout "){";
		print_break 0 2;
		open_vbox 0;
		print_stmt_list stmt_list;
		close_box ();
		print_cut ();
		shout "}";
	| Stmt_define (id, fields, exp) ->
		print_id id;
		print_fields fields;
		shout " = ";
		print_exp exp;
		shout ";";
	| Stmt_function_call (id, exps) ->
		print_funcall (id, exps);
		shout ";";
	| Stmt_return x ->
		shout "return ";
		print_exp_option x;
		shout ";";
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
		shout "(";
		print_exp_list exps;
		shout ")";;

let rec print_fargs = function
	| Fargs [] -> ()
	| Fargs [a] ->
		print_id a;
	| Fargs (a::list) ->
		print_id a;
		shout ", ";
		print_fargs (Fargs list);;

let print_basictype = function
	| Type_int -> shout "Int";
	| Type_bool -> shout "Bool";
	| Type_char -> shout "Char";;

let rec print_typetoken = function
	| Basictype b -> print_basictype b;
	| Type_tuple (t1, t2) ->
		shout "(";
		print_typetoken t1;
		shout ", ";
		print_typetoken t2;
		shout ")";
	| Type_list t ->
		shout "[";
		print_typetoken t;
		shout "]";
	| Type_id id ->
		print_id id;;

let print_rettype = function
	| Type_void ->
		shout "Void";
	| Rettype t ->
		print_typetoken t;;

let rec print_funtype = function
	| Funtype ([], ret) ->
		shout "-> ";
		print_rettype ret;
		shout " ";
	| Funtype (a::list, ret) ->
		print_typetoken a;
		shout " ";
		print_funtype (Funtype (list, ret));;

let print_var_option = function
	| None ->
		shout "var";
	| Some t ->
		print_typetoken t;;

let rec print_vardecl = function
	| Vardecl (t, id, exp) ->
		print_var_option t;
		shout " ";
		print_id id;
		shout " = ";
		print_exp exp;
		shout ";";;

let rec print_vardecl_list = function
	| [] -> ();
	| x::list -> 
		print_vardecl x;
		print_cut ();
		print_vardecl_list list;;

let print_funtype_option = function
	| None -> ();
	| Some ft ->
		shout " :: ";
		print_funtype ft;;

let rec print_fundecl = function
	| Fundecl (id, fargs, funtype, vardecl_list, stmt_list) ->
		print_id id;
		shout "(";
		print_fargs fargs;
		shout ")";
		print_funtype_option funtype;
		shout "{";
		print_break 0 2;
		open_vbox 0;
		print_vardecl_list vardecl_list;
		print_stmt_list stmt_list;
		close_box ();
		print_cut ();
		shout "}";;

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
		print_newline ();
		print_newline ();
		print_spl (SPL list);;
