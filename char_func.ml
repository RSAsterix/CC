open String
open Bytes
open Char
open List

(* === string to char list === *)
(* explode maakt een char list, implode een string *)
(* nodig voor pattern matching op strings *) 

let explode s =
  let rec expl i l =
    if i < 0 then l else
    expl (i - 1) (s.[i] :: l) in
  expl (String.length s - 1) [];;

let implode l =
  let result = Bytes.create (List.length l) in
  let rec imp i = function
  | [] -> result
  | c :: l -> result.[i] <- c; imp (i + 1) l in
  imp 0 l;;

(* let is_whitespace = function                                 *)
(*   | ' ' | '\010' | '\013' | '\009' | '\026' | '\012' -> true *)
(*   | _ -> false                                               *)

let is_digit c =
	'0' <= c && c <= '9'
let is_uppercase c =
	'A' <= c && c <= 'Z'
let is_lowercase c =
	'a' <= c && c <= 'z'
let is_letter c =
  is_uppercase c || is_lowercase c
