open Types
open Char_func
open Format

(* print "True" als het argument true is,*)
(* en "False" als het argument false is. *)
let print_bool ppf = function
	| true -> fprintf ppf "%s" "True";
	| false -> fprintf ppf "%s" "False";;

(* print de string van een Id *)
let print_id ppf = function
	| Id id -> fprintf ppf "%s" id;;

(* print de integer van een Inttoken *)
let print_inttoken ppf = function
	| Inttoken i -> fprintf ppf "%i" i;;

(* print de operator van een Op1 *)
let print_op1 ppf = function
	| Not -> fprintf ppf "!";
	| Neg -> fprintf ppf "-";;

(* print de operator van een Op2 *)
let print_op2 ppf = function
	| Listop -> fprintf ppf ":"
	| Logop And -> fprintf ppf "&&"
	| Logop Or -> fprintf ppf "||"
	| Eqop Eq -> fprintf ppf "=="
	| Eqop Neq -> fprintf ppf "!="
	| Compop Less -> fprintf ppf "<"
	| Compop Greater -> fprintf ppf ">"
	| Compop LeEq -> fprintf ppf "<="
	| Compop GrEq -> fprintf ppf ">="
	| Strongop Times -> fprintf ppf "*"
	| Strongop Divide -> fprintf ppf "/"
	| Strongop Modulo -> fprintf ppf "%%"
	| Weakop Plus -> fprintf ppf "+"
	| Weakop Minus -> fprintf ppf "-";;

(* print een lijst van fields met punten ertussen *)
let rec print_fields ppf = function
	| [] -> ();
	| Hd::ls -> fprintf ppf "%a.hd" print_fields ls;
	| Tl::ls -> fprintf ppf "%a.tl" print_fields ls;
	| Fst::ls -> fprintf ppf "%a.fst" print_fields ls;
	| Snd::ls -> fprintf ppf "%a.snd" print_fields ls;;

(* levert het niveau van sterkte van een operator *)
(* hoe hoger, hoe sterker                         *)
let op_map = function
	| Listop -> 1
	| Logop _ -> 2
	| Eqop _ -> 3
	| Compop _ -> 3
	| Weakop _ -> 4
	| Strongop _ -> 5;;

(* Levert true als de eerste expressie een infix-expressie is *)
(* met een zwakkere operator                                  *)
let isLower exp op = match exp with
	| Exp_infix (e1, o, e2) -> (op_map o) < (op_map op);
	| e -> false;;

(* Print een expressie *)
let rec print_exp ppf = function
	| Exp_field (id, flds) -> fprintf ppf "%a%a" print_id id print_fields flds;
	| Exp_infix (exp1, op2, exp2) -> 
		fprintf ppf "(%a" print_exp exp1;
		fprintf ppf " %a " print_op2 op2;
		fprintf ppf "%a)" print_exp exp2;
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
(* Print een statement *)
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
(* Nodig omdat een returnstatement misschien een expressie heeft, *)
(* of misschien void                                              *)
and print_exp_option ppf = function
	| None -> ();
	| Some exp -> fprintf ppf "%a" print_exp exp;
(* Print een function call *)
and print_funcall ppf = function
	| (id, exps) -> fprintf ppf "%a(%a)" print_id id print_exp_list exps;;

(* Print een lijst van function arguments *)
let rec print_fargs ppf = function
	| Fargs [] -> ()
	| Fargs [a] ->
		fprintf ppf "%a" print_id a;
	| Fargs (a::list) ->
		fprintf ppf "%a, %a" print_id a print_fargs (Fargs list);;

(* Print basictypes int, bool of char *)
let print_basictype ppf = function
	| Type_int -> fprintf ppf "%s" "Int";
	| Type_bool -> fprintf ppf "%s" "Bool";
	| Type_char -> fprintf ppf "%s" "Char";;

(* Print een typetoken *)
let rec print_typetoken ppf = function
	| Basictype b -> fprintf ppf "%a" print_basictype b;
	| Type_tuple (t1, t2) -> fprintf ppf "(%a, %a)" print_typetoken t1 print_typetoken t2;
	| Type_list t -> fprintf ppf "[%a]" print_typetoken t;
	| Type_id id -> fprintf ppf "%a" print_id id;;

(* Print een returntype, wordt gebruikt in print_funtype *)
let print_rettype ppf = function
	| Type_void -> fprintf ppf "%s" "Void";
	| Rettype t -> fprintf ppf "%a" print_typetoken t;;

(* Print een functietype *)
let rec print_funtype ppf = function
	| Funtype ([], ret) -> fprintf ppf "-> %a " print_rettype ret;
	| Funtype (a::list, ret) -> fprintf ppf "%a %a" print_typetoken a print_funtype (Funtype (list, ret));;

(* Nodig omdat een vardecl ofwel 'var' heeft, ofwel een type *)
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
