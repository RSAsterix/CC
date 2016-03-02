Dit project bevat de tokenizer en parser voor de taal SPL, gemaakt door Tom Evers en Martin Huijben.
Het is geschreven in de taal OCaml.

Het bevat de volgende modules:
 - char_func.ml
 	OCaml's build-in char functions zijn maar schamel. char_func vult dit aan. 
 	Het bevat ook functies om operators te herkennen.
 - types.ml
 	In deze module staan alle zelf-gedefinieerde types. Het bestaat uit 3 delen:
 	structure: dit is de boom die de parser teruggeeft
 	result: als het de parser lukt om een structure te maken, geeft het Success(structure), anders geeft het een Error(foutmeldingstring)
	
 - tokenizer.ml
	Deze module bevat twee grote functies met hulpfuncties:
	-scan_line: leest een char list en maakt een token list
	-token_list_to_string: leest een token list en maakt een string
 - parser.ml
	Dit is verreweg de grootste module. Het beste is om deze module van onder naar boven te lezen. De hoofdfunctie is spl_parser, die gegeven [] en een tokenlist ofwel Succes(spl) teruggeeft, ofwel Error(foutmeldingstring)
	
	
	
 - pretty_printer_files.ml
	Iedere functie krijgt het argument "ppf"  mee. Dit argument is een zogeheten 'formatter': als het ware een outputstream met extra functionaliteit.
	Iedere functie levert een unit van de vorm 
		fprintf ppf "<formatting>" <arguments>
	Een formatting is in principe een string die geprint wordt naar ppf, met enkele speciale tokens:
		%x			-	print het eerstvolgende nog niet gebruikte argument
		@[<v x>		-	opent een zogenaamde 'vertical box', waarin alle output gelijk uitgelijnd wordt met de positie waarin de box wordt aangeroepen (offset x)
		@]			-	sluit de vorige box
		@,			-	print een enter
		@;<0 x>		-	print een enter, met de volgende regel op een offset van x
	
 - test.ml
	Deze module wordt uiteindelijk uitgevoerd.
	Het leest het bestand regel voor regel in, en geeft de resulterende tokenlist mee aan de functie "spl_parser" in parser.ml
	Geeft spl_parser een error, dan wordt de error geprint
	Geeft spl_parser een structuur terug, dan wordt deze meegegeven aan de prettyprinter (pretty_printer_files.ml)