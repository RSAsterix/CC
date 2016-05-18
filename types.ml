(*==    structure    ==*)
type id = string
type constructor = string
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
	| Exp_int of int
	| Exp_char of char
	| Exp_bool of bool
	| Exp_function_call of id * exp list
	| Exp_emptylist
	| Exp_tuple of exp * exp
	| Exp_low_bar
	| Exp_constructor of constructor
type stmt = 
	| Stmt_if of exp * stmt list
	| Stmt_if_else of exp * stmt list * stmt list
	| Stmt_while of exp * stmt list
	| Stmt_define of fieldexp * exp
	| Stmt_function_call of id * exp list
	| Stmt_return of exp option
	| Stmt_match of exp * (exp * stmt list) list
type fargs = id list
type typetoken = Type_int | Type_bool | Type_char
	| Type_tuple of typetoken * typetoken
	| Type_list of typetoken
	| Type_id of id
type rettype = Rettype of typetoken | Type_void
type funtype = typetoken list * rettype
type vardecl = typetoken option * id * exp 
type fundecl = id * fargs * funtype option * vardecl list * stmt list
type typedecl = Rename of id * typetoken | Enum of id * constructor list
type decl = Typedecl of typedecl | Vardecl of vardecl | Fundecl of fundecl
type spl = decl list;;


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
	| Basic_int | Basic_bool | Basic_char
	| IF | ELSE | WHILE | RETURN
	| FALSE | TRUE
	| PERIOD 
	| Fieldtoken of field
	| Optok of string
	| Inttok of int
	| IDtok of string
	| Constructortok of string
	| Chartok of char
	| Startcomment
	| Endcomment
	| LOWBAR
	| TYPE 
	| MATCH
	| WITH
	| PIPE;;
