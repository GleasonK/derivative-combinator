let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let rec reduce f l = 
	match l with
	| [] 		-> failwith "List of size 2 required for reduction."
	| x1::[] 	-> x1
	| x1::x2::xs -> 
		let red = f x1 x2 in
		reduce f (red::xs);;

type parser = 
	| Empty
	| Epsilon
	| Token of char
	| Seq of parser lazy_t * parser lazy_t
	| Alt of parser lazy_t * parser lazy_t
	| Refr of parser ref;;

let memo f =
  let m = ref [] in
    fun x ->
      try
        List.assoc x !m
      with
      Not_found ->
        let y = f x in
          m := (x, y) :: !m ;
          y;;

let memo2d f =
	let m = ref [] in
	fun x y ->
	  try
	  	let cache2 = ref (List.assoc x !m) in
	  	  try
	  		List.assoc y !cache2
	  	  with
	  	  Not_found ->
	  	  	let res = f x y in
	  	  	cache2 := (y,res) :: !cache2;
	  	  	res
	  with
	  Not_found ->
	  	let res = f x y in
	  	let m2 = ref [] in
	  	m2 := (y, res) :: !m2;
	  	m  := (x, !m2) :: !m;
	  	res;;

let force l = 
	match l with
	| Alt(l1, l2) -> (Lazy.force l1, Lazy.force l2)
	| Seq(l1, l2) -> (Lazy.force l1, Lazy.force l2)
	| _ -> failwith "Invalid input.";;

let rec nullable (parser : parser) =
	match parser with
	| Empty 	 -> false
	| Epsilon 	 -> true
	| Token c 	 -> false
	| Alt(l1,l2) -> 
	  let l1f, l2f = force parser in
	  nullable l1f || nullable l2f
	| Seq(l1,l2) ->
	  let l1f, l2f = force parser in
	  nullable l1f && nullable l2f
    | Refr l     -> false;; (* Need to fix first *)

let isEmpty (parser : parser) = 
	match parser with
	| Empty -> true
	| _ 	-> false;;

let isEpsilon (parser : parser) =
	match parser with
	| Epsilon -> true
	| _ 	  -> false;;

let rec compactF (parser : parser) = 
	match parser with
	| Empty 	-> parser
	| Epsilon 	-> parser
	| Token c 	-> parser
	| Alt(l1,l2)	->
		let l1f, l2f = force parser in
		if isEmpty l1f then compact l2f
		else if isEmpty l2f then compact l1f
		else
			let l1c, l2c = (compact l1f, compact l2f) in
			Alt(lazy(l1c), lazy(l2c))
	| Seq(l1,l2) ->
		let l1f,l2f = force parser in
		if (isEmpty l1f || isEmpty l2f) then Empty
		else if isEpsilon l1f then compact l2f
		else if isEpsilon l2f then compact l1f
		else
			let l1c, l2c = (compact l1f, compact l2f) in
			Seq(lazy(l1c), lazy(l2c))
	| Refr l     -> compact !l

and compact parser = compactF parser;; (* Need to memoize *)

let alt2 = memo (fun l1 l2 -> compact(Alt(lazy(l1), lazy(l2))));;

let seq2 = memo (fun l1 l2 -> compact(Seq(lazy(l1),lazy(l2))));;

let alt (parsers : parser list) = reduce alt2 (Empty::parsers);;

let seq (parsers : parser list) = reduce seq2 (Epsilon::parsers);;

let rec deriveF c parser =
	match parser with
	| Empty 	-> Empty
	| Epsilon 	-> Empty
	| Token tok -> 
		if c = tok then Epsilon
		else Empty
	| Alt(l1,l2) ->
		let l1f,l2f = force parser in
		alt [derive c l1f; derive c l2f]
	| Seq(l1,l2) ->
		let l1f,l2f = force parser in
		let der = seq [derive c l1f; l2f] in 
		if nullable l1f then alt [der; derive c l2f]
		else der
	| Refr l     -> derive !l
and derive c parser = deriveF c parser;; (* Need to Memoize *)

let rec size (parser : parser) =
	match parser with
	| Empty 	 -> 1
	| Epsilon 	 -> 1
	| Token c 	 -> 1
	| Alt(l1,l2) -> 
		let l1f, l2f = force parser in
		1 + size l1f + size l2f
	| Seq(l1,l2) ->
		let l1f, l2f = force parser in
		1 + size l1f + size l2f
    | Refr l     -> 0;;

let parses parser str = (* Works for strings not tokens. *)
	let rec partialParse parser chars =
		match chars with
		| [] 	-> nullable parser
		| c::cs -> partialParse (derive c parser) cs
	in
		let chars = explode str in
		partialParse parser chars;;

(* DEBUG / TESTING *)

let rec lit charArray =
	match charArray with
	| [] 	-> []
	| c::cs -> (Token c)::(lit cs);;

let literal litr =
	let charArray = explode litr in
	seq (lit charArray);;

let string_lits litr =
	let charArray = explode litr in
	lit charArray;;

let printParser parser = 
	let rec printIt parser =
		match parser with
		| Empty 	-> print_string "Empty"
		| Epsilon 	-> print_string "Epsilon"
		| Token c 	-> Printf.printf "Token %c" c
		| Alt(l1,l2) 	->
			let l1f, l2f = force parser in
			print_string "Alt(";
			printIt l1f;
			print_string ", ";
			printIt l2f;
			print_string ")"
		| Seq(l1,l2) 	->
			let l1f, l2f = force parser in
			print_string "Seq(";
			printIt l1f;
			print_string ", ";
			printIt l2f;
			print_string ")"
	in
	    printIt parser;
	    Printf.printf "\n";;

let mini_java =
    let space = Token ' ' in
    let alphabet = alt (string_lits "abcdefghijklmnopqrstuvwxyz") in
    let capAlpha = alt (string_lits "ABCDEFGHIJKLMNOPQRSTUVWXYZ") in
    let optChar = alt ([alphabet; capAlpha; Epsilon]) in
    let prims = alt ([literal "void"; literal "boolean";  literal "byte"; literal "char"; literal "short"; literal "int"; literal "float"; literal "double"; literal "long"]) in
    let jClass = seq [capAlpha; optChar; optChar; optChar; optChar; optChar; optChar; optChar;] in
    (* let ADTyp = seq [literal "<"; 'a'; literal ">"] in *)
    let access = alt ([literal "private"; literal "public"; literal "abstract"]) in
    let retTyp = alt ([jClass; prims]) in
    let funct = seq [alphabet; optChar; optChar; optChar; optChar; optChar; optChar; optChar; optChar; optChar]; in
    let parens = literal "()" in
    let mini_java = seq [access; space; retTyp; space; funct; parens] in
    mini_java;;

let test_parser = Seq (lazy(Alt(lazy (Token 'x'), lazy(Token 'y'))), lazy(Epsilon));;
let tp_size = size test_parser;;
let tp_nullable = nullable test_parser;;
Printf.printf "Is Nullable: %B\n" tp_nullable;;
Printf.printf "Parse size: %d\n" tp_size;;
printParser test_parser;;

let mini_java_string_good = "public void fxn()";;
let mini_java_string_bad  = "pubblc none fxn()";;
let parses_string_good = parses mini_java mini_java_string_good;;
let parses_string_bad  = parses mini_java mini_java_string_bad;;
