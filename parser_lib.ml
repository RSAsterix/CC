open Char_func
open Types
open Printf
open Tokenizer

let err_unex line expected found =
	Error (sprintf "(r.%i) Expected '%s', but found '%s'" line (token_to_string expected) (token_to_string found));;
let vardecl_message = "If this is a variable declaration, you probably forgot the type or the 'var' keyword.";;
let err_unex_extra line expected found = Error (
		sprintf "(r.%i) Expected '%s', but found '%s'\n%s" 
		line 
		(token_to_string expected) 
		(token_to_string found) 
		vardecl_message
		);;
let err_unex_unknown line found = Error (
		sprintf "(r.%i) Unexpected token: '%s'"
		line 
		(token_to_string found)
		);;
let err_eof line after = 
	Error (sprintf "(r.%i) Unexpected EOF after '%s'" line (token_to_string after));;
let err_eof_end parse =
	Error (sprintf "Unexpected EOF while parsing %s." parse);;