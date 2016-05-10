open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer_files

open Graph_make
open Graph_lib
open Graph_cycles
open Graph_print

open Typechecker
open Typechecker_types
open Typechecker_lib
open Typechecker_print

(* #directory "C:/Users/tom_e/workspace/CC/_build";; *)
(* open Printf;;                                     *)
(* #load "char_func.cmo";;                           *)
(* open Char_func;;                                  *)
(* #load "types.cmo";;                               *)
(* open Types;;                                      *)
(* #load "graph_lib.cmo";;                           *)
(* open Graph_lib;;                                  *)
(* #load "graph_make.cmo";;                          *)
(* open Graph_make;;                                 *)
(* #load "graph_cycles.cmo";;                        *)
(* open Graph_cycles;;                               *)
(* #load "tokenizer.cmo";;                           *)
(* open Tokenizer;;                                  *)
(* #load "exp_parser.cmo";;                          *)
(* open Exp_parser;;                                 *)
(* #load "parser.cmo";;                              *)
(* open Parser;;                                     *)
(* #load "pretty_printer_files.cmo";;                *)
(* open Pretty_printer_files;;                       *)
(* #load "typechecker_types.cmo";;                   *)
(* open Typechecker_types;;                          *)
(* #load "typechecker_print.cmo";;                   *)
(* open Typechecker_print;;                          *)
(* #load "typechecker_lib.cmo";;                     *)
(* open Typechecker_lib;;                            *)
(* #load "typechecker.cmo";;                         *)
(* open Typechecker;;                                *)
(* #use "test.ml";;                                  *)

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

let unpack res = match res with
| Success x -> x
| Error e -> raise (Invalid_argument e);;

let filename = "C:/Users/Tom/workspace/CC/inputT.txt";;
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
	match m (Env_var.empty, Env_fun.empty) x with
	| Error e -> print_endline e;
	| Success env -> print_endline (prettyprint_env env);;
(* close_out oc;; *)