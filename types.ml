type id = Id of char list
type inttoken = Inttoken of char list
type op1 = Op1 of char
type op2 = Op2 of char list
type fieldtoken = Hd | Tl | Fst | Snd
type field = Field of fieldtoken list
type exp = 
	| Exp_field of id * field
	| Exp_infix of exp * op2 * exp
	| Exp_prefix of op1 * exp
	| Exp_int of inttoken
	| Exp_char of char
	| Exp_bool of bool
	| Exp_parentheses of exp
	| Exp_function_call of id * exp list
	| Exp_emptylist
	| Exp_tuple of exp * exp
type stmt = 
	| Stmt_if of exp *  stmt list
	| Stmt_if_else of exp *  stmt list *  stmt list
	| Stmt_while of exp *  stmt list
	| Stmt_define of id * field * exp
	| Stmt_function_call of id *  exp list
	| Stmt_return of exp option
type fargs = Fargs of id list
type basictype = Type_int | Type_bool | Type_char
type typetoken =  Basictype of basictype
	| Type_tuple of typetoken * typetoken
	| Type_list of typetoken
	| Type_id of id
type rettype = Rettype of typetoken | Type_void
type funtype = Funtype of typetoken list * rettype
type vardecl = Vardecl_var of id * exp | Vardecl_type of typetoken * id * exp 
type fundecl = Fundecl of id * fargs * funtype option * vardecl list * stmt list
type decl = Decl_var of vardecl | Decl_fun of fundecl
type spl = SPL of decl list;;

type 'a result = Error of string | Success of 'a;;


type token = 
	| VAR
	| EQ
	| SEMICOLON
	| OPEN_PAR | CLOSE_PAR 
	| DDPOINT
	| OPEN_ACO | CLOSE_ACO
	| VOID
	| ARROW
	| COMMA
	| OPEN_BRACK | CLOSE_BRACK
	| Basictoken of basictype
	| IF | ELSE | WHILE | RETURN
	| FALSE | TRUE
	| EMPTYLIST
	| PERIOD 
	| Fieldtoken of fieldtoken
	| Optok of char list
	| Inttok of char list
	| IDtok of char list
	| Chartok of char;;