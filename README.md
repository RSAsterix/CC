Dit project bevat de tokenizer en parser voor de taal SPL, gemaakt door Tom Evers en Martin Huijben.
Het is geschreven in de taal OCaml.

Het bevat de volgende modules:
 - char_func.ml
 	OCaml's build-in char functions zijn maar schamel. char_func vult dit aan. 
 	Het bevat ook functies om operators te herkennen.
 - types.ml
 	In deze module staan alle zelf-gedefinieerde types. Het bestaat uit 3 delen:
 	structure: dit is de boom die de parser teruggeeft
 	result: als het de parser lukt om een structure te maken, geeft het Success(structure), anders geeft het een
 	 
 	