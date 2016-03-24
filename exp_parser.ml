open Types
open Printf
open Tokenizer

type aso = Left | Right
type opstruct = 
	{
		op : op2;
		opval : int; (*hoe lager hoe sterker*)
		aso : aso; (*asociativiteit*)
	}

type tlt = (int*token) list (*TokenListType*)

(* 				De Exp Parser				*)
(* Bij deze parser is wel wat uitleg nodig *)
(* Eerst wat definities: *)
(* - atom: *)
(* 				Een expressie zonder infix operators buiten haakjes *)
(* - opstruct: *)
(* 				Een infix operator, met toegevoegde informatie, *)
(* 				namelijk zijn binding strength en zijn associativiteit *)
(* - de exp van een opstruct: *)
(* 				De Exp_infix, waarbij de middelste waarde opstruct.op is. *)
(* - winnen: *)
(* 				Opstruct1 wint van opstruct2 als de exp van opstruct2 ergens in de exp van opstruct1 hoort. *)
(* 				Anders wint opstruct2. *)
(* 				Dit hangt af van binding strength en associativiteit van beide opstructs *)
(* - expleft, opstruct1, expbetween, opstruct2, expright: *)
(* 				De infix_operator vergelijkt twee opstructs, opstruct1 en opstruct2. *)
(* 				Daar links, rechts en tussen van bevinden zich expressies *)
(* - waitlist: *)
(* 				De waitlist is gevuld met (expressie,opstruct) tuples, *)
(* 				waarvoor geldt dat elke opstruct verliest van de opstruct die er na komt *)
(* 				Elke opstruct in waitlist wint altijd van opstruct1*)
(* - fitten: *)
(* 				Een opstruct fit tussen twee andere opstructs als hij wint van de ene *)
(* 				en verliest van de ander. Hij past er als het ware tussen *)


(* De exp parser bestaat uit 3 delen: *)
(* - exp_parser: de functie die de twee andere delen aanroept *)
(* - infix_parser: de functie die een boom maakt van atoms en infix operators *)
(* - atom_parser: de functie die een atom oplevert *)
(* De exp_parser en atom_parser zijn vrij standaard *)
(* De infix_parser is recursief, met als base case dat er geen expressie meer te parsen is van de list.*)
(* Op dat moment hebben we nog over een linkse expressie, een opstruct, een rechte expressie en een waitlist *)
(* De functie empty_waitlist wordt aangeroepen om de waitlist te legen. Deze functie levert een expressie op. *)

(* Hoe werkt de infix_parser? *)
(* Als er maar 1 opstruct, is de taak simpel. Return de exp van de opstruct *)
(* Als er twee zijn (opstruct1 en opstruct2), moeten we uitvinden welke operator wint: *)
(* - Als opstruct1 wint van opstruct2: *)
(* 		Opstruct1 en expleft worden toegevoegd aan de waitlist. *)
(* 		De infix_parser gaat verder met opstruct2 als de nieuwe opstruct1 *)
(* - Als opstruct2 wint van opstruct1: *)
(* 	  Elke opstruct in de waitlist wint ook van opstruct1, dus *)
(* 	  we moeten kijken of er opstructs in waitlist zijn die tussen opstruct1 en opstruct2 fitten *)
(* 	  Hiervoor is de functie fit_waitlist. *)
(* 		Deze functie krijgt de waitlist, de expressie van opstruct1 (hij heeft verloren en zijn expressie is dus klaar) en opstruct2 *)
(* 		De functie maakt net zolang nieuwe expressies van de opstructs in de waitlist, *)
(* 		totdat de opstruct van hd waitlist wint van opstruct2 (of tot de waitlist leeg is) *)
(* 		Vervolgens gaat de infix_parser verder met opstruct2 als de nieuwe opstruct1 *)
(* Als de er niets meer te parsen valt, roept de infix_parser empty_waitlist aan. *)


(* field = '.' fieldtoken [field] *)
(* fieldtoken = 'hd' | 'tl' | 'fst' | 'snd' *)
let rec field_parser (field_list:field list) (list:tlt): field list result * tlt = match list with
	| (_,PERIOD)::(_,Fieldtoken t)::list -> field_parser (t::field_list) list
	| (_,PERIOD)::(l,x)::list -> Error (sprintf "(r.%i) No field, but: %s" l (token_to_string x)), (l,x)::list
	| (l,PERIOD)::[] -> Error (sprintf "(r.%l) Unexpected EOF while parsing a field." l), []
	| list -> Success (List.rev field_list), list;;

(* a+b:tail betekent a + (b:tail)*)
 
let parse_op1 (list:tlt):op1 option * tlt = match list with
	| (_,Optok "!")::list -> Some Not, list
	| (_,Optok "-")::list -> Some Neg, list
	| list -> None, list

let opstruct_parser list :(opstruct option * tlt) = match list with
	| (_,Optok ":")::list -> Some{op = Listop; opval = 0; aso = Right}, list
	| (_,Optok "*")::list -> Some{op = Strongop Times; opval = 1; aso = Left}, list
  | (_,Optok "/")::list -> Some{op = Strongop Divide; opval = 1; aso = Left}, list
  | (_,Optok "%")::list -> Some{op = Strongop Modulo; opval = 1; aso = Left}, list
  | (_,Optok "+")::list -> Some{op = Weakop Plus; opval = 2; aso = Left}, list
  | (_,Optok "-")::list -> Some{op = Weakop Minus; opval = 2; aso = Left}, list
  | (_,Optok "==")::list -> Some{op = Eqop Eq; opval = 3; aso = Left}, list
  | (_,Optok "!=")::list -> Some{op = Eqop Neq; opval = 3; aso = Left}, list
  | (_,Optok "<")::list -> Some{op = Compop Less; opval = 3; aso = Left}, list
  | (_,Optok ">")::list -> Some{op = Compop Greater; opval = 3; aso = Left}, list
  | (_,Optok "<=")::list -> Some{op = Compop LeEq; opval = 3; aso = Left}, list
  | (_,Optok ">=")::list -> Some{op = Compop GrEq; opval = 3; aso = Left}, list
  | (_,Optok "&&")::list -> Some{op = Logop And; opval = 4; aso = Left}, list
  | (_,Optok "||")::list -> Some{op = Logop Or; opval = 5; aso = Left}, list
	| list -> None, list

let wins left right = (left.opval > right.opval) || (left.opval == right.opval && left.aso=Right)

let rec empty_waitlist waitlist expbetween opstruct expright = match waitlist with
| [] -> Success(Exp_infix(expbetween,opstruct.op,expright))
| (wexp,wop)::restwaitlist ->
	if wins wop opstruct then
		empty_waitlist restwaitlist wexp wop (Exp_infix(expbetween,opstruct.op,expright))
	else
		empty_waitlist restwaitlist (Exp_infix(wexp,wop.op,expbetween)) opstruct expright

let rec fit_waitlist waitlist expbetween opstruct = match waitlist with
| [] -> ([],expbetween)
| (wexp,wop)::restwaitlist ->
	if wins wop opstruct then
		(waitlist,expbetween)
	else
		fit_waitlist restwaitlist (Exp_infix(wexp,wop.op,expbetween)) opstruct

let rec exp_parser list :  (exp result * tlt) = 
	match atom_parser list with 
	| Success (None), (l,x)::list -> Error (sprintf "(r.%i) No expression, but: %s" l (token_to_string x)), (l,x)::list
	| Error e, list -> Error e, list
	| Success x, [] -> Error "Unexpected EOF while expression was expected", [] 
	| Success (Some expleft), list -> 
		match opstruct_parser list with
		| None, list -> Success expleft, list
		| Some opstruct, list ->
			match atom_parser list with
			| Success (None), (l,x)::list -> Error (sprintf "(r.%i) No expression after infix operator, but: %s" l (token_to_string x)), (l,x)::list
			| Success (None), [] -> Error "Unexpected EOF while expression was expected", [] 
			| Error e, list -> Error e, list
			| Success (Some expright), list -> infix_parser [] (expleft) (opstruct) (expright) (list)
and
infix_parser (waitlist:(exp*opstruct)list)(expleft:exp) (opstruct1:opstruct) (expbetween:exp) (list:tlt) :exp result*tlt = 
	match opstruct_parser list with
	| Some opstruct2, list ->
  	(match atom_parser list with
		| Success (None), (l,x)::list -> Error (sprintf "(r.%i) No expression after infix operator, but: %s" l (token_to_string x)), (l,x)::list
		| Success (None), [] -> Error "Unexpected EOF after infix operator", []
		| Error e, list -> Error e, list
  	| Success (Some expright), list -> 
			if wins opstruct1 opstruct2 then
				infix_parser ((expleft,opstruct1)::waitlist) (expbetween) (opstruct2) (expright) (list)
			else 	
				(match fit_waitlist (waitlist) (Exp_infix(expleft,opstruct1.op,expbetween)) (opstruct2) with
				| newwaitlist,expbetween -> infix_parser (newwaitlist) (expbetween) (opstruct2) (expright) (list)))				
	| None, list -> empty_waitlist waitlist expleft opstruct1 expbetween, list
and
(* expStrongest =	int                 *)
(* 							| char                *)
(* 							| 'False'             *)
(* 							| 'True'              *)
(* 							| '[]'                *)
(* 							| id funcall          *)
(* 							| id field            *)
(* 							| '(' exp ',' exp ')' *)
(* 							| '(' exp ')'         *)
(* 							| op1 exp             *)
atom_parser (list:tlt): (exp option result* tlt) = match list with
	| (_,Inttok i)::list -> Success (Some (Exp_int i)), list
	| (_,Chartok c)::list -> Success (Some (Exp_char c)), list
	| (_,FALSE)::list -> Success (Some (Exp_bool false)), list
	| (_,TRUE)::list -> Success (Some (Exp_bool true)), list
	| (_,EMPTYLIST)::list -> Success (Some (Exp_emptylist)), list
	| (_,IDtok id)::(_,OPEN_PAR)::list -> 
		(match funcall_parser list with
		| Success exps, list -> Success (Some (Exp_function_call ((Id id), exps))), list 
		| Error e, list -> Error e, list)
	|	(_,IDtok id)::list -> 
		(match field_parser [] list with
		| Success fieldlist, list -> Success (Some (Exp_field (Id id, fieldlist))), list
		| Error e, list -> Error e, list)
	| (l0,OPEN_PAR)::list -> 
		(match (exp_parser list) with
		| Success exp1, (l1,COMMA)::list -> 
			(match (exp_parser list) with
			| Success exp2, (_,CLOSE_PAR)::list -> Success (Some (Exp_tuple (exp1,exp2))), list
			| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis after comma, but: %s" l (token_to_string x)), (l,x)::list
			| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after comma." l1), []
			| Error e, list -> Error e, list)
		| Success exp, (_,CLOSE_PAR)::list -> Success (Some exp), list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error (sprintf "(r.%i) Unexpected EOF after opening parenthesis." l0), [] 
		| Error e, list -> Error e, list)
	| list ->
		(match parse_op1 list with
		| Some op, list ->
			(match (exp_parser list) with
  		| Success exp, list ->  Success (Some (Exp_prefix (op, exp))), list
  		| Error e, list -> Error e, list)
		| None, list -> Success (None), list)
and
(* funcall = ')' | actargs *)
funcall_parser (list:tlt) :(exp list result * tlt) =
	(* actargs = exp ')' | exp ',' actargs *)
	let rec actargs_parser arg_list list = (match (exp_parser list) with
		| Success exp, (_,CLOSE_PAR)::list -> Success (List.rev (exp::arg_list)), list
		| Success exp, (_,COMMA)::list -> actargs_parser (exp::arg_list) list
		| Success _, (l,x)::list -> Error (sprintf "(r.%i) No closing parenthesis or comma, but: %s" l (token_to_string x)), (l,x)::list
		| Success _, [] -> Error "Unexpected EOF while parsing function arguments.", []
		| Error e, list -> Error e, list) in
	match list with
	| (_,CLOSE_PAR)::list -> Success([]), list
	| list -> actargs_parser [] list;;