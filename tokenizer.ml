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

let rec token_list_to_string list = match list with
	| [] -> "" 
	| VAR::list -> "VAR, " ^ token_list_to_string(list)
	| EQ::list -> "EQ, " ^ token_list_to_string(list)
	| SEMICOLON::list -> ";, " ^ token_list_to_string(list)
	| OPEN_PAR::list -> "(, " ^ token_list_to_string(list)
	| CLOSE_PAR::list -> "), " ^ token_list_to_string(list)
	| DDPOINT::list -> "::, " ^ token_list_to_string(list)
	| OPEN_ACO::list -> "{, " ^ token_list_to_string(list)
	| CLOSE_ACO::list -> "}, " ^ token_list_to_string(list)
	| VOID::list -> "VOID, " ^ token_list_to_string(list)
	| ARROW::list -> "->, " ^ token_list_to_string(list)
	| COMMA::list -> "COMMA, " ^ token_list_to_string(list)
	| OPEN_BRACK::list -> "[, " ^ token_list_to_string(list)
	| CLOSE_BRACK::list -> "], " ^ token_list_to_string(list)
	| Basictoken Type_int::list -> "INT, " ^ token_list_to_string(list)
	| Basictoken Type_bool::list -> "BOOL, " ^ token_list_to_string(list)
	| Basictoken Type_char::list -> "CHAR, " ^ token_list_to_string(list)
	| IF::list -> "IF, " ^ token_list_to_string(list)
	| ELSE::list -> "ELSE, " ^ token_list_to_string(list)
	| WHILE::list -> "WHILE, " ^ token_list_to_string(list)
	| RETURN::list -> "RETURN, " ^ token_list_to_string(list)
	| FALSE::list -> "FALSE, " ^ token_list_to_string(list)
	| TRUE::list -> "TRUE, " ^ token_list_to_string(list)
	| EMPTYLIST::list -> "[], " ^ token_list_to_string(list)
	| PERIOD::list -> "., " ^ token_list_to_string(list)
	| Fieldtoken a::list -> "FIELDTOKEN, " ^ token_list_to_string(list)
	| Optok a::list -> "OP " ^ (implode a) ^ ", " ^ token_list_to_string(list)
	| Inttok a::list -> "INTTOK " ^ (implode a) ^ ", " ^ token_list_to_string(list)
	| IDtok a::list -> "ID " ^ (implode a) ^ ", " ^ token_list_to_string(list)