open Char_func
open Types
open List


let rec get_number number line = match line with
		| char::restline -> 
			if is_digit char 
			then get_number (char::number) restline 
			else (Some (Inttok (int_of_string (implode (List.rev number)))), line)
		| [] -> (Some (Inttok (int_of_string (implode (List.rev number)))),line);;

let rec get_name name line = match line with
		| char::restline -> 
			if is_letter char || is_digit char || char == '_' 
			then get_name (char::name) restline 
			else (Some (IDtok (implode (List.rev name))),line)
		| [] -> (Some (IDtok (implode (List.rev name))),line);;

(*Checkt of het keywoord dat we al gelezen hebben niet direct gevolgd wordt door een letter of cijfer.*)
(*Dan is het namelijk geen keyword maar een id*)
let match_next line = line == [] || (not(is_letter (List.hd line)) && not(is_digit (List.hd line)));;

let rec scan_line l = function
	| [] -> []
	| 'v'::'a'::'r'::line when (match_next line) -> (l, VAR)::(scan_line l line)
	| 'V'::'o'::'i'::'d'::line when (match_next line) -> (l, VOID)::(scan_line l line)
	| 'I'::'n'::'t'::line when (match_next line) -> (l, Basic_int)::(scan_line l line)
	| 'B'::'o'::'o'::'l'::line when (match_next line) -> (l, Basic_bool)::(scan_line l line)
	| 'C'::'h'::'a'::'r'::line when (match_next line) -> (l, Basic_char)::(scan_line l line)
	| 'i'::'f'::line when (match_next line) -> (l, IF)::(scan_line l line)
	| 'e'::'l'::'s'::'e'::line when (match_next line) -> (l, ELSE)::(scan_line l line)
	| 'w'::'h'::'i'::'l'::'e'::line when (match_next line) -> (l, WHILE)::(scan_line l line)
	| 'r'::'e'::'t'::'u'::'r'::'n'::line when (match_next line) -> (l, RETURN)::(scan_line l line)
	| 'F'::'a'::'l'::'s'::'e'::line when (match_next line) -> (l, FALSE)::(scan_line l line)
	| 'T'::'r'::'u'::'e'::line when (match_next line) -> (l, TRUE)::(scan_line l line)
	| 'h'::'d'::line when (match_next line) -> (l, Fieldtoken Hd)::(scan_line l line)
	| 't'::'l'::line when (match_next line) -> (l, Fieldtoken Tl)::(scan_line l line)
	| 'f'::'s'::'t'::line when (match_next line) -> (l, Fieldtoken Fst)::(scan_line l line)
	| 's'::'n'::'d'::line when (match_next line) -> (l, Fieldtoken Snd)::(scan_line l line)
	| ':'::':'::line -> (l, DDPOINT)::(scan_line l line)
	| '-'::'>'::line -> (l, ARROW)::(scan_line l line)
	| '['::']'::line -> (l, EMPTYLIST)::(scan_line l line)
	| '/'::'/'::line -> []
	| '/'::'*'::line -> (l, Startcomment)::(scan_line l line)
	| '*'::'/'::line -> (l, Endcomment)::(scan_line l line)
	| '.'::line -> (l, PERIOD)::(scan_line l line)
	| '+'::line -> (l, Optok "+")::(scan_line l line)
	| '-'::line -> (l, Optok "-")::(scan_line l line)
	| '*'::line -> (l, Optok "*")::(scan_line l line)
	| '/'::line -> (l, Optok "/")::(scan_line l line)
	| '%'::line -> (l, Optok "%")::(scan_line l line)
	| '='::'='::line -> (l, Optok "==")::(scan_line l line)
	| '<'::'='::line -> (l, Optok "<=")::(scan_line l line)
	| '>'::'='::line -> (l, Optok ">=")::(scan_line l line)
	| '!'::'='::line -> (l, Optok "!=")::(scan_line l line)
	| '&'::'&'::line -> (l, Optok "&&")::(scan_line l line)
	| '|'::'|'::line -> (l, Optok "||")::(scan_line l line)
	| ':'::line -> (l, Optok ":")::(scan_line l line)
	| '!'::line -> (l, Optok "!")::(scan_line l line)
	| '<'::line -> (l, Optok "<")::(scan_line l line)
	| '>'::line -> (l, Optok ">")::(scan_line l line)
	| '='::line -> (l, EQ)::(scan_line l line) 
	| ';'::line -> (l, SEMICOLON)::(scan_line l line)
	| '('::line -> (l, OPEN_PAR)::(scan_line l line)
	| ')'::line -> (l, CLOSE_PAR)::(scan_line l line)
	| '{'::line -> (l, OPEN_ACO)::(scan_line l line)
	| '}'::line -> (l, CLOSE_ACO)::(scan_line l line)
	| ','::line -> (l, COMMA)::(scan_line l line)
	| '['::line -> (l, OPEN_BRACK)::(scan_line l line)
	| ']'::line -> (l, CLOSE_BRACK)::(scan_line l line)
	| '\''::c::'\''::line -> (l, (Chartok c))::(scan_line l line)
	| char::line -> match
			 (if is_digit char then (get_number [] (char::line))
      	else if is_letter char then (get_name [] (char::line))
      	else (None, line)) with
    		| None,line -> scan_line l line
    		| Some s, line -> (l, s)::(scan_line l line);;

let token_to_string t = match t with
	| VAR -> "var "
	| EQ -> "="
	| SEMICOLON -> ";"
	| OPEN_PAR -> "("
	| CLOSE_PAR -> ")"
	| DDPOINT -> "::"
	| OPEN_ACO -> "{"
	| CLOSE_ACO -> "}"
	| VOID -> "Void"
	| ARROW -> "->"
	| COMMA -> ","
	| OPEN_BRACK -> "["
	| CLOSE_BRACK -> "]"
	| EMPTYLIST -> "[]"
	| Basic_int -> "Int"
	| Basic_bool -> "Bool"
	| Basic_char -> "Char"
	| IF -> "if"
	| ELSE -> "else"
	| WHILE -> "while"
	| RETURN -> "return"
	| FALSE -> "False"
	| TRUE -> "True"
	| PERIOD -> "."
	| Fieldtoken Hd -> "hd"
	| Fieldtoken Tl -> "tl"
	| Fieldtoken Fst -> "fst"
	| Fieldtoken Snd -> "snd"
	| Optok a -> a
	| Inttok a -> string_of_int a
	| IDtok a -> a
	| Chartok a -> implode ['\'';a;'\''] 
	| Startcomment -> "/* "
	| Endcomment -> " */" ;;

let rec token_list_to_string list = match list with
	| [] -> "" 
	| (_,t)::list -> (token_to_string t) ^ (token_list_to_string list);;
