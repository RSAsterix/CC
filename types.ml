(*==    structure    ==*)
type id = Id of string
type inttoken = Inttoken of int
type op1 = Not | Neg
type logop = And | Or
type eqop = Eq | Neq
type compop = Less | Greater | LeEq | GrEq
type strongop = Times | Divide | Modulo
type weakop = Plus | Minus
type op2 = 
	| Listop 
	| Logop of logop 
	| Eqop of eqop
	| Compop of compop
	| Weakop of weakop
	| Strongop of strongop
type field = Hd | Tl | Fst | Snd
type fieldexp = 
	| Nofield of id
	| Field of fieldexp * field
type exp = 
	| Exp_field of fieldexp
	| Exp_infix of exp * op2 * exp
	| Exp_prefix of op1 * exp
	| Exp_int of inttoken
	| Exp_char of char
	| Exp_bool of bool
	| Exp_function_call of id * exp list
	| Exp_emptylist
	| Exp_tuple of exp * exp
type stmt = 
	| Stmt_if of exp *  stmt list
	| Stmt_if_else of exp *  stmt list *  stmt list
	| Stmt_while of exp *  stmt list
	| Stmt_define of fieldexp * exp
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
type vardecl = Vardecl of typetoken option * id * exp 
type fundecl = Fundecl of id * fargs * funtype option * vardecl list * stmt list
type decl = Decl_var of vardecl | Decl_fun of fundecl
type spl = SPL of decl list;;


(*==    result    ==*)
type 'a result = Error of string | Success of 'a;;


(*==    token    ==*)
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
	| EMPTYLIST
	| OPEN_BRACK | CLOSE_BRACK
	| Basictoken of basictype
	| IF | ELSE | WHILE | RETURN
	| FALSE | TRUE
	| PERIOD 
	| Fieldtoken of field
	| Optok of string
	| Inttok of int
	| IDtok of string
	| Chartok of char;;
