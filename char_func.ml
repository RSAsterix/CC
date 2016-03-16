open String
open Bytes
open Char
open List

(*van string naar char list*)
let explode s =
  let rec expl i l =
    if i < 0 then l else
    expl (i - 1) (s.[i] :: l) in
  expl (String.length s - 1) [];;

(*van char list naar string*)
let implode l =
  let result = Bytes.create (List.length l) in
  let rec imp i = function
  | [] -> result
  | c :: l -> Bytes.set result i c; imp (i + 1) l in
  imp 0 l;;

let is_digit = function
  | '0'..'9' -> true
  | _ -> false;;

let is_uppercase c = 'A' <= c && c <= 'Z';;
let is_lowercase c = 'a' <= c && c <= 'z';;

let is_letter c =
  is_uppercase c || is_lowercase c;;

let is_op1 = function
	| Optok "!" -> true
	| Optok "-" -> true
	| _ -> false;;

let is_op_colon = function
	| Optok ":" -> true
	| _ -> false;;

let is_op_logical c =
	c = "||" || c = "&&";;

let is_op_eq c =
	c = "==" || c = ">=" || c = "<=" || c = "!=" || c = "<" || c = ">";;

let is_op_plus c =
	c = "+" || c = "-";;

let is_op_times c =
	c = "*" || c = "/" || c = "%";;

let op2_to_type = function
	| Op2 ":" -> Listop
	| Op2 "&&" -> Logop And
	| Op2 "||" -> Logop Or
	| Op2 "==" -> Eqop Eq
	| Op2 "!=" -> Eqop Neq
	| Op2 "<" -> Compop Less
	| Op2 ">" -> Compop Greater
	| Op2 "<=" -> Compop LeEq
	| Op2 ">=" -> Compop GrEq
	| Op2 "*" -> Strongop Times
	| Op2 "/" -> Strongop Divide
	| Op2 "%" -> Strongop Modulo
	| Op2 "+" -> Weakop Plus
	| Op2 "-" -> Weakop Minus;;

let op1_to_type = function
	| Op1 "!" -> Not
	| Op2 "-" -> Neg 