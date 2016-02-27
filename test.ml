open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

let filename = "C:/Users/tom_e/workspace/CC/input3.txt";;
(* let filename = "C:/Users/Martin/workspace/test/input.txt";; *)

let in_channel = open_in filename;;
let tokenlist = ref [];;
try
  while true do
    let line = input_line in_channel in
		let tokenlistline = scan_line (explode line) in
    print_endline (token_list_to_string (tokenlistline));
		tokenlist := List.append !tokenlist tokenlistline
	done
with End_of_file ->
  close_in in_channel;;

let structure = spl_parser [] !tokenlist;;
match structure with
| Error e -> print_endline e 
| Success x -> print_spl x;;