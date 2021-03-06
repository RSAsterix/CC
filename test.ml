open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer_files
open Code_generator
open Codefragments
open Rewrite_match_casings

open Graph_make
open Graph_lib
open Graph_cycles
open Graph_print

open Typechecker
open Typechecker_types
open Typechecker_lib
open Typechecker_print

open Format

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
(* #load "codefragments.cmo";;                       *)
(* open Codefragments;;                              *)
(* #load "code_generator.cmo";;                      *)
(* open Code_generator;;                             *)
(* #use "test.ml";;                                  *)

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

let unpack res = match res with
| Success x -> x
| Error e -> raise (Invalid_argument e);;

let filename = "inputenum"


let unpack res = match res with
| Success x -> x
| Error e -> raise (Invalid_argument e);;

let filename = "inputenum"

let in_channel =
	try
		open_in ("C:/Users/tom_e/workspace/CC/"^filename^".txt")
	with
	| _ -> open_in ("C:/Users/Martin/workspace/CC/"^filename^".txt");;

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

let structure = parser [] !tokenlist;;
(* let outfile = "C:/Users/tom_e/workspace/CC/output.txt";; *)
let outfile = "C:/Users/Martin/workspace/CC/output.txt";;
(* let oc = open_out outfile;; *)

(* (*types of input4 *)                                                                                                      *)
(* let vartypes4 = [("b",Int)];;                                                                                             *)
(* let funtypes4 = [{fid="facI";ftype=Imp(Int,Int);locals=[("r",Int)]}];;                                                    *)

(* (*types of input7 *)                                                                                                      *)
(* let vartypes7 = [("p",Lis Int);("ft",Lis Int);("r",Lis Int);("sc",Tup (Lis Int,Bool));("s",Tup(Int,Int));("a",Lis Int)];; *)
(* let funtypes7 = [                                                                                                         *)
(* 	{fid="product";ftype=Imp (Lis Int,Int);locals=[]};                                                                      *)
(* 	{fid="fromTo";ftype=Imp(Int, Imp (Int,Lis Int));locals=[]};                                                             *)
(* 	{fid="reverse";ftype=Imp(Lis (Var "a"),Lis (Var "a"));locals=[("accu",Lis (Var "a"))]};                                 *)
(* 	{fid="swapCopy";ftype=Imp(Tup(Var "a",Var "b"),Tup(Var "b",Var "a"));locals=[]};                                        *)
(* 	{fid="swap";ftype=Imp(Tup(Var "a",Var "a"),Tup(Var "a",Var "a"));locals=[("tmp",Var "a")]};                             *)
(* 	{fid="append";ftype=Imp(Lis Int,Imp(Lis Int,Lis Int));locals=[]}                                                        *)
(* 	];;                                                                                                                     *)

match structure with
| Error e -> print_endline e;
| Success x -> 
			(* print_spl std_formatter (rmc_spl (snd x)); *)
  match m x with
  | Error e -> print_endline e;
  | Success env -> 
		print_endline (code_gen env (rmc_spl (snd x)));;
		(* print_string (prettyprint_env env);; *)
(* close_out oc;; *)