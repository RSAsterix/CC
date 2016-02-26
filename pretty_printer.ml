let rec print_stmt_list = function
	| [] -> ()
	| stmt::list -> print_stmt stmt; print_stmt_list list
and
print_stmt = function
	| Stmt_if (exp ,stmt_list) -> 
		print "if(";
		print_exp exp;
		print_line"){";
		print_smt_list stmt_list;
		print_line"}"
	| Stmt_if_else (exp , stmt_list1 ,  stmt_list2) -> 
		print "if(";
		print_exp exp;
		print_line"){";
		print_stmt_list stmt_list1;
		print_line"}else{";
		print_stmt_list stmt_list2;
		print_line"}"
	| Stmt_while (exp ,  stmt_list) ->
		print "while(";
		print_exp exp;
		print_line"){";
		print_smt_list stmt_list;
		print_line"}"
	| Stmt_define (id , field , exp) ->
		print_id id;
		print_field field;
		print "=";
		print_exp exp;
		print_line ";";
	| Stmt_function_call (id ,  exp_list) ->
		print_id id;
		print "(";
		print_exp_list exp_list;
		print_line ")";
	| Stmt_return None ->
		print_line "return;"
	| Stmt_return Some exp ->
		print_exp exp;
		print_line ";"




