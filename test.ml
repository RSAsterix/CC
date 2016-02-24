open Printf
open Tokenizer
open Parser

(* === code die file reading regelt. === *)
(* Hierna kun je een regel uit het bestand krijgen door *)
(* (Stream.next lines) aan te roepen *)

let filename = "C:/Users/Martin/workspace/test/input.txt";;
(*let filename = "./input.txt";;*)


(* === string to char list === *)
(* explode maakt een char list, implode een string *)
(* nodig voor pattern matching op strings *) 


	


let tokenlist=[];
let in_channel = open_in filename in
try
  while true do
    let line = input_line in_channel in
		tokenlistline= scan_line (explode line)
    print_endline (token_list_to_string (tokenlistline));
		tokenlist = append tokenlist tokenlistline
  done
with End_of_file ->
  close_in in_channel; 



	

(*in de def van exp staat dat een exp een char kan zijn. Ik snap niet waarvoor dat is*)
(*let er op bij de compiler maken, dat onze infix operators gestructureerd zijn van links naar rechts ipv * boven + *)
(*waarom staat er een id achter Fargs?*)	 

