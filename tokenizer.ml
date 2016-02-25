open Char_func
open Types
open List


let rec get_number number line = match line with
		| char::restline -> 
			if is_digit char 
			then get_number (char::number) restline 
			else (Some (Inttok (List.rev number)),line)
		| [] -> (Some (Inttok (List.rev number)),line)

let rec get_name name line = match line with
		| char::restline -> 
			if is_letter char || is_digit char || char == '_' 
			then get_name (char::name) restline 
			else (Some (IDtok (List.rev name)),line)
		| [] -> (Some (IDtok (List.rev name)),line)

let match_next line = line == [] || (not(is_letter (List.hd line)) && not(is_digit (List.hd line)));;

let rec scan_line = function
	| [] -> []
	| 'v'::'a'::'r'::line when (match_next line) -> VAR::(scan_line line)
	| 'V'::'o'::'i'::'d'::line when (match_next line) -> VOID::(scan_line line)
	| 'I'::'n'::'t'::line when (match_next line) -> Basictoken Type_int ::(scan_line line)
	| 'B'::'o'::'o'::'l'::line when (match_next line) -> Basictoken Type_bool ::(scan_line line)
	| 'C'::'h'::'a'::'r'::line when (match_next line) -> Basictoken Type_char ::(scan_line line)
	| 'i'::'f'::line when (match_next line) -> IF ::(scan_line line)
	| 'e'::'l'::'s'::'e'::line when (match_next line) -> ELSE ::(scan_line line)
	| 'w'::'h'::'i'::'l'::'e'::line when (match_next line) -> WHILE ::(scan_line line)
	| 'r'::'e'::'t'::'u'::'r'::'n'::line when (match_next line) -> RETURN ::(scan_line line)
	| 'F'::'a'::'l'::'s'::'e'::line when (match_next line) -> FALSE ::(scan_line line)
	| 'T'::'r'::'u'::'e'::line when (match_next line) -> TRUE ::(scan_line line)
	| 'h'::'d'::line when (match_next line) -> Fieldtoken Hd ::(scan_line line)
	| 't'::'l'::line when (match_next line) -> Fieldtoken Tl::(scan_line line)
	| 'f'::'s'::'t'::line when (match_next line) -> Fieldtoken Fst::(scan_line line)
	| 's'::'n'::'d'::line when (match_next line) -> Fieldtoken Snd::(scan_line line)
	| ':'::':'::line -> DDPOINT::(scan_line line)
	| '-'::'>'::line -> ARROW::(scan_line line)
	| '['::']'::line -> EMPTYLIST::(scan_line line)
	| '.'::line -> PERIOD::(scan_line line)
	| '+'::line -> Optok(['+'])::(scan_line line)
	| '-'::line -> Optok(['-'])::(scan_line line)
	| '*'::line -> Optok(['*'])::(scan_line line)
	| '/'::line -> Optok(['/'])::(scan_line line)
	| '%'::line -> Optok(['%'])::(scan_line line)
	| '<'::'='::line -> Optok(['<';'='])::(scan_line line)
	| '>'::'='::line -> Optok(['>';'='])::(scan_line line)
	| '!'::'='::line -> Optok(['!';'='])::(scan_line line)
	| '&'::'&'::line -> Optok(['&';'&'])::(scan_line line)
	| '|'::'|'::line -> Optok(['|';'|'])::(scan_line line)
	| ':'::line -> Optok([':'])::(scan_line line)
	| '!'::line -> Optok(['!'])::(scan_line line)
	| '<'::line -> Optok(['<'])::(scan_line line)
	| '>'::line -> Optok(['>'])::(scan_line line)
	| '='::line -> EQ::(scan_line line) 
	| ';'::line -> SEMICOLON::(scan_line line)
	| '('::line -> OPEN_PAR::(scan_line line)
	| ')'::line -> CLOSE_PAR::(scan_line line)
	| '{'::line -> OPEN_ACO::(scan_line line)
	| '}'::line -> CLOSE_ACO::(scan_line line)
	| ','::line -> COMMA::(scan_line line)
	| '['::line -> OPEN_BRACK::(scan_line line)
	| ']'::line -> CLOSE_BRACK::(scan_line line)
	| char::line -> match
			 (if is_digit char then (get_number [] (char::line))
      	else if is_letter char then (get_name [] (char::line))
      	else (None, line)) with
    		| None,line -> scan_line line
    		| Some s, line -> s::(scan_line line)

let token_to_string t = match t with
	| VAR -> "var"
	| EQ -> " = "
	| SEMICOLON -> "; "
	| OPEN_PAR -> "("
	| CLOSE_PAR -> ")"
	| DDPOINT -> " :: "
	| OPEN_ACO -> "{"
	| CLOSE_ACO -> "}"
	| VOID -> "Void"
	| ARROW -> " -> "
	| COMMA -> ","
	| OPEN_BRACK -> "["
	| CLOSE_BRACK -> "]"
	| Basictoken Type_int -> "Int"
	| Basictoken Type_bool -> "Bool"
	| Basictoken Type_char -> "Char"
	| IF -> "if "
	| ELSE -> "else "
	| WHILE -> "while "
	| RETURN -> "return "
	| FALSE -> "False"
	| TRUE -> "True"
	| EMPTYLIST -> "[]"
	| PERIOD -> "."
	| Fieldtoken Hd -> "hd"
	| Fieldtoken Tl -> "tl"
	| Fieldtoken Fst -> "fst"
	| Fieldtoken Snd -> "snd"
	| Optok a -> implode a
	| Inttok a -> implode a
	| IDtok a -> implode a;;

let rec token_list_to_string list = match list with
	| [] -> "" 
	| t::list -> (token_to_string t) ^ (token_list_to_string list);;

