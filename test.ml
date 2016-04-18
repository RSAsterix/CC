open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer_files

open Graph_make
open Graph_lib
open Graph_cycles

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

(* let filename = "C:/Users/tom_e/workspace/CC/input.txt";; *)
let filename = "C:/Users/Martin/workspace/CC/inputT.txt";;

let in_channel = open_in filename;;
let tokenlist = ref [];;
let l = ref 0;;
try
  while true do
    let line = input_line in_channel in
		l := !l + 1;
		let tokenlistline = scan_line !l (explode line) in
    (* print_endline (token_list_to_string (tokenlistline)); *)
		tokenlist := List.append !tokenlist tokenlistline
	done
with End_of_file ->
  close_in in_channel;;

let structure = spl_parser [] !tokenlist;;
let outfile = "C:/Users/tom_e/workspace/CC/output.txt";;
(* let outfile = "C:/Users/Martin/workspace/CC/output.txt";; *)
(* let oc = open_out outfile;; *)
match structure with
| Error e -> print_endline e;
| Success x -> print_spl (Format.formatter_of_out_channel stdout) x;;
(* close_out oc;; *)