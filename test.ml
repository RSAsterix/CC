open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer_files
open Typechecker
open Typechecker_lib

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

(* open Printf;;                      *)
(* #load "char_func.cmo";;            *)
(* open Char_func;;                   *)
(* #load "types.cmo";;                *)
(* open Types;;                       *)
(* #load "typechecker_lib.cmo";;      *)
(* open Typechecker_lib;;             *)
(* #load "type_graph.cmo";;           *)
(* open Type_graph;;                  *)
(* #load "spl_to_graph.cmo";;         *)
(* open Spl_to_graph;;                *)
(* #load "cycledetection.cmo";;       *)
(* open Cycledetection;;              *)
(* #load "tokenizer.cmo";;            *)
(* open Tokenizer;;                   *)
(* #load "exp_parser.cmo";;           *)
(* open Exp_parser;;                  *)
(* #load "parser.cmo";;               *)
(* open Parser;;                      *)
(* #load "typechecker.cmo";;          *)
(* open Typechecker;;                 *)
(* #load "pretty_printer_files.cmo";; *)
(* open Pretty_printer_files;;        *)
(* #use "test.ml";;                   *)


let filename = "C:/Users/tom_e/workspace/CC/input2.txt";;
(* let filename = "C:/Users/Tom/workspace/CC/input.txt";; *)
(* let filename = "C:/Users/Martin/workspace/CC/inputT.txt";; *)

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
| Success x ->
	(match m environment x with
	| Error error -> print_endline error; 
	| Success x ->
		print_endline (prettyprint_env x);)
 		(* print_spl (Format.formatter_of_out_channel stdout) x);; *)
(* close_out oc;; *)