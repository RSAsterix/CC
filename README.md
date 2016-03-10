Dit project bevat de tokenizer, parser en prettyprinter voor de taal SPL, gemaakt door Tom Evers en Martin Huijben.
Het is geschreven in de taal OCaml.

Het bevat de volgende modules:
 - char_func.ml
 	OCaml's build-in char functions zijn maar schamel. char_func vult dit aan. 
 	Het bevat ook functies om operators te herkennen.
 - types.ml
 	In deze module staan alle zelf-gedefinieerde types. Het bestaat uit 3 delen:
 	structure: dit is de boom die de parser teruggeeft
 	result: als het de parser lukt om een structure te maken, geeft het Success(structure), anders geeft het een Error(foutmeldingstring)
	token: alle tokens
 - tokenizer.ml
	Deze module bevat twee grote functies met hulpfuncties:
	-scan_line: leest een char list en maakt een token list
	-token_list_to_string: leest een token list en maakt een string
 - parser.ml
	Dit is verreweg de grootste module. Deze module is het beste van onder naar boven te lezen. De hoofdfunctie is spl_parser, die gegeven [] en een tokenlist ofwel Success(spl) teruggeeft, ofwel Error(foutmeldingstring). Deze functie roept via-via alle bovengelegen functies aan, die elk een deel van de structuur maken.
	Een paar opmerkingen:
	 - functies hebben standaard een naam van de vorm x_parser, waarbij x het deel van de structuur is die ze teruggeven.
	 - functies hebben standaard een output van de vorm Success(structuurdeel,restlist). Als functies worden aangeroepen, moeten ze unpacked worden. Dat gebeurt met de code:
		match functie-aanroep with
		| (structuurdeel,restlist) -> do_something
	 - Errorstrings hebben een vorm van "(functie waar de error voorkwam)" plus een optionele "Previous vardecl failed. " plus ("No x, but: " of "Unexpected token: ") plus de tokenlist
	 - list parsers (inclusief fargs_parser) snoepen standaard een ')' of een '}' van de tokenlist, met uitzondering van vardecl_list_parser, die net zolang parset totdat hij een Error tegenkomt. Alle list parsers kunnen [] teruggeven.
	 - functies kunnen elkaar niet circulair aanroepen, tenzij het keyword and is gebruikt. Dit is het geval bij stmt_parser en stmt_list_parser en bij het parsen van exp.	
 - pretty_printer_files.ml
	Deze module prettyprints naar een file.
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
	Het leest het in de code gespecificeerde bestand regel voor regel in, en geeft de resulterende tokenlist mee aan de functie "spl_parser" in parser.ml
	Geeft spl_parser een error, dan wordt de error geprint
	Geeft spl_parser een structuur terug, dan wordt deze meegegeven aan de prettyprinter (pretty_printer_files.ml)
	Op dit moment print het naar de console. Verander stdout naar oc om naar output.txt te printen
	
Verder bevat ons project de volgende tekstbestanden:
 - grammar
 - input1, voorbeeldcode spl
 - input2, meer voorbeeldcode spl
 - output, de output van input2
 - inputT, voorbeeldcode om de exp_parser te testen