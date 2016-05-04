open Printf
open Tokenizer
open Parser
open Char_func
open Types
open Pretty_printer_files
open Code_generator
open Codefragments

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

(* let filename = "C:/Users/tom_e/workspace/CC/input.txt";; *)
let filename = "C:/Users/Martin/workspace/CC/input7.txt";;

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

(*types of input4 *)
let vartypes4 = [("b",Int)];;
let funtypes4 = [{fid="facI";ftype=Imp(Int,Int);locals=[("r",Int)]}];;

(*types of input7 *)
let vartypes7 = [("p",Lis Int);("ft",Lis Int);("r",Lis Int);("sc",Tup (Lis Int,Bool));("s",Tup(Int,Int));("a",Lis Int)];;
let funtypes7 = [
	{fid="product";ftype=Imp (Lis Int,Int);locals=[]};
	{fid="fromTo";ftype=Imp(Int, Imp (Int,Lis Int));locals=[]};
	{fid="reverse";ftype=Imp(Lis (Var "a"),Lis (Var "a"));locals=[("accu",Lis (Var "a"))]};
	{fid="swapCopy";ftype=Imp(Tup(Var "a",Var "b"),Tup(Var "b",Var "a"));locals=[]};
	{fid="swap";ftype=Imp(Tup(Var "a",Var "a"),Tup(Var "a",Var "a"));locals=[("tmp",Var "a")]};
	{fid="append";ftype=Imp(Lis Int,Imp(Lis Int,Lis Int));locals=[]}
	];;

match structure with
| Error e -> print_endline ((token_list_to_string (!tokenlist)) ^ e);
| Success x -> print_string (code_gen vartypes7 funtypes7 x);;
	(* print_spl (Format.formatter_of_out_channel stdout) x;; *)
(* close_out oc;; *)