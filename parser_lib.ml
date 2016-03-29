open Char_func
open Types
open Printf
open Tokenizer

let err_unexpected line expected found =
	Error (sprintf "(r.%i) Expected '%s', but found '%s'" line (token_to_string expected) (token_to_string found));;
let err_eof line after = 
	Error (sprintf "(r.%i) Unexpected EOF after '%s'" line (token_to_string after));;