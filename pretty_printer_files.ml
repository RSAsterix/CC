open Types
open Char_func
open Format

let print_bool ppf = function
	| true -> fprintf ppf "%s" "True";
	| false -> fprintf ppf "%s" "False";;

let print_id ppf = function
	| Id id -> fprintf ppf "%s" id;;

let print_inttoken ppf = function
	| Inttoken i -> fprintf ppf "%i" i;;

let print_op1 ppf = function
	| Op1 o -> fprintf ppf "%s" o;;

let print_op2 ppf = function
	| Op2 o -> fprintf ppf "%s" o;;

let rec print_fields ppf = function
	| Field [] -> ();
	| Field (Hd::ls) -> fprintf ppf "%a.hd" print_fields (Field ls);
	| Field (Tl::ls) -> fprintf ppf "%a.tl" print_fields (Field ls);
	| Field (Fst::ls) -> fprintf ppf "%a.fst" print_fields (Field ls);
	| Field (Snd::ls) -> fprintf ppf "%a.snd" print_fields (Field ls);;

let op_map = function
	| Op2 c when (is_op_colon c) -> 1
	| Op2 c when (is_op_logical c) -> 2
	| Op2 c when (is_op_eq c) -> 3
	| Op2 c when (is_op_plus c) -> 4
	| Op2 c when (is_op_times c) -> 5;;

let isLower exp op = match exp with
	| Exp_infix (e1, o, e2) -> (op_map o) < (op_map op);
	| e -> false;;

let rec print_exp ppf = function
	| Exp_field (id, flds) -> fprintf ppf "%a%a" print_id id print_fields flds;
	| Exp_infix (exp1, op2, exp2) ->  
		(if(isLower exp1 op2) 
		then(fprintf ppf "(%a)" print_exp exp1;)
		else(fprintf ppf "%a" print_exp exp1;));	
		fprintf ppf " %a " print_op2 op2;
		(if(isLower exp2 op2)
		then(fprintf ppf "(%a)" print_exp exp2;)
		else(fprintf ppf "%a" print_exp exp2;));
	| Exp_prefix (op1, exp) ->
		fprintf ppf "%a%a" print_op1 op1 print_exp exp;
	| Exp_int int ->
		fprintf ppf "%a" print_inttoken int;
	| Exp_char c -> fprintf ppf "'%c'" c;
	| Exp_bool b -> fprintf ppf "%a" print_bool b;
	| Exp_function_call (id, exps) -> fprintf ppf "%a" print_funcall (id, exps);
	| Exp_emptylist -> fprintf ppf "%s" "[]";
	| Exp_tuple (exp1, exp2) ->
		fprintf ppf "(%a,%a)" print_exp exp1 print_exp exp2;
and print_exp_list ppf = function
	| [] -> ();
	| [exp] ->
		fprintf ppf "%a" print_exp exp;
	| exp::exp_list ->
		fprintf ppf "%a, %a" print_exp exp print_exp_list exp_list;
and print_stmt ppf = function
	| Stmt_if (exp, stmt_list) ->
		fprintf ppf "if(%a){@;<0 2>@[<v 0>%a@]@,}" print_exp exp print_stmt_list stmt_list;
	| Stmt_if_else (exp, stmt_list1, stmt_list2) -> 
		fprintf ppf "if(%a){@;<0 2>@[<v 0>%a@]@,}else{@;<0 2>@[<v 0>%a@]@,}" print_exp exp print_stmt_list stmt_list1 print_stmt_list stmt_list2; 
	| Stmt_while (exp, stmt_list) ->
		fprintf ppf "while(%a){@;<0 2>@[<v 0>%a@]@,}" print_exp exp print_stmt_list stmt_list;
	| Stmt_define (id, fields, exp) ->
		fprintf ppf "%a%a = %a;" print_id id print_fields fields print_exp exp;
	| Stmt_function_call (id, exps) ->
		fprintf ppf "%a;" print_funcall (id, exps)
	| Stmt_return x ->
		fprintf ppf "return %a;" print_exp_option x;
and print_stmt_list ppf = function
	| [] -> ();
	| [stmt] ->
		fprintf ppf "%a" print_stmt stmt;
	| stmt::ls ->
		fprintf ppf "%a@,%a" print_stmt stmt print_stmt_list ls;
and print_exp_option ppf = function
	| None -> ();
	| Some exp -> fprintf ppf "%a" print_exp exp;
and print_funcall ppf = function
	| (id, exps) -> fprintf ppf "%a(%a)" print_id id print_exp_list exps;;

let rec print_fargs ppf = function
	| Fargs [] -> ()
	| Fargs [a] ->
		fprintf ppf "%a" print_id a;
	| Fargs (a::list) ->
		fprintf ppf "%a, %a" print_id a print_fargs (Fargs list);;

let print_basictype ppf = function
	| Type_int -> fprintf ppf "%s" "Int";
	| Type_bool -> fprintf ppf "%s" "Bool";
	| Type_char -> fprintf ppf "%s" "Char";;

let rec print_typetoken ppf = function
	| Basictype b -> fprintf ppf "%a" print_basictype b;
	| Type_tuple (t1, t2) -> fprintf ppf "(%a, %a)" print_typetoken t1 print_typetoken t2;
	| Type_list t -> fprintf ppf "[%a]" print_typetoken t;
	| Type_id id -> fprintf ppf "%a" print_id id;;

let print_rettype ppf = function
	| Type_void -> fprintf ppf "%s" "Void";
	| Rettype t -> fprintf ppf "%a" print_typetoken t;;

let rec print_funtype ppf = function
	| Funtype ([], ret) -> fprintf ppf "-> %a " print_rettype ret;
	| Funtype (a::list, ret) -> fprintf ppf "%a %a" print_typetoken a print_funtype (Funtype (list, ret));;

let print_var_option ppf = function
	| None -> fprintf ppf "%s" "var";
	| Some t -> fprintf ppf "%a" print_typetoken t;;

let rec print_vardecl ppf = function
	| Vardecl (t, id, exp) -> fprintf ppf "%a %a = %a;" print_var_option t print_id id print_exp exp;;

let rec print_vardecl_list ppf = function
	| [] -> ();
	| x::list -> fprintf ppf "%a@,%a" print_vardecl x print_vardecl_list list;;

let print_funtype_option ppf = function
	| None -> ();
	| Some ft -> fprintf ppf " :: %a" print_funtype ft;;

let rec print_fundecl ppf = function
	| Fundecl (id, fargs, funtype, vardecl_list, stmt_list) -> 
		fprintf ppf "%a(%a)%a{@;<0 2>@[<v 0>%a%a@]@,}" print_id id print_fargs fargs print_funtype_option funtype print_vardecl_list vardecl_list print_stmt_list stmt_list;;

let print_decl ppf = function
	| Decl_var v -> fprintf ppf "%a" print_vardecl v;
	| Decl_fun f -> fprintf ppf "%a" print_fundecl f;;

let rec print_spl ppf = function
	| SPL [] -> ();
	| SPL (x::list) -> fprintf ppf "@[<v 0>%a@]@.@.%a" print_decl x print_spl (SPL list);;
