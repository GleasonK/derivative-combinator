open System
open System.Text
open System.Collections.Generic
  
module String =
  let explode (s:string) =
    [for c in s -> c]

module Fix = 
  let fix body bottom = 
    let Cache = new Dictionary<_, _>()
    let Visited = new Dictionary<_,bool>()
    let changed = ref true
    let running = ref false
    let rec f = fun parser -> 
      if not !running then
        if Cache.ContainsKey(parser) then Cache.[parser]
        else
          changed := true
          running := true
          Visited.Clear()
          let v = ref bottom
          while (!changed) do
            changed := false
            Visited.Clear()
            v := (f parser)
          !v
      else
        if Visited.ContainsKey(parser) then 
          if Cache.ContainsKey(parser) then Cache.[parser] else bottom
        else
            Visited.Add(parser, true)
            let value = body parser
            if Cache.ContainsKey(parser) then
              if Cache.[parser] <> value then
                changed := true
                Cache.[parser] <- value
                value
              else
                value
            else
                Cache.Add(parser, value)
                value
    fun parser -> f parser

module Parser =
  let memoize f =
    let cache = Dictionary<_, _>()
    fun x ->
      if cache.ContainsKey(x) then cache.[x]
      else 
        let res = f x
        cache.[x] <- res
        res
  
  let memo2d f =
    let cache = Dictionary<_, Dictionary<_,_>>()
    fun p c ->
      if cache.ContainsKey(p) then 
        let cache2 = cache.[p]
        if cache2.ContainsKey(c) then cache2.[c]
        else
          let res = f p c
          cache2.[c] <- res
          res
      else 
        let resDic = Dictionary<_, _>()
        cache.[p] <- resDic
        let res = f p c
        resDic.[c] <- res
        res
  
  (*[<StructuralEquality;StructuralComparison>]*)
  type ParseSet =
    | EmptyS
    | EpsilonS
    | EpsParseS of HashSet<ParseSet>
    | Cons of ParseSet * ParseSet
    | TokenS of char

  type Parser = 
    | Empty
    | Epsilon
    | EpsS of HashSet<ParseSet>
    | Token of char
    | Alt of Lazy<Parser> * Lazy<Parser>
    | Seq of Lazy<Parser> * Lazy<Parser>
  
  let (|Seqp|_|) parser =
    match parser with
      | Seq(l1,l2) -> Some(l1.Force(), l2.Force())
      | _          -> None

  let (|Altp|_|) parser =
    match parser with
      | Alt(l1,l2) -> Some(l1.Force(), l2.Force())
      | _          -> None
  
  (* Checks if a Parser is nullable - Uses Least Fixed Point *)
  let rec nullableF parser =
    match parser with
      | Empty       -> false
      | Epsilon     -> true
      | Token c     -> false
      | Altp(l1,l2) -> nullable l1 || nullable l2
      | Seqp(l1,l2) -> nullable l1 && nullable l2
      | _ -> false
  and nullable = Fix.fix nullableF false

  (* Active Pattern Matchers *)
  let (|Nullablep|_|) parser = if nullable parser then Some(parser) else None
  
  let isEpsilon parser =
    match parser with
      | Epsilon -> true
      | _       -> false 

  let rec isEmptyF parser =
    match parser with
      | Empty       -> true
      | Epsilon     -> false
      | Token c     -> false
      | Altp(l1,l2) -> isEmpty l1 && isEmpty l2
      | Seqp(l1,l2) -> isEmpty l1 || isEmpty l2
      | _ -> false
  and isEmpty = Fix.fix isEmptyF true
  
  let rec isNullF parser = 
    match parser with
      | Empty       -> false
      | Epsilon     -> true
      | Token c     -> false
      | Altp(l1,l2) -> isNull l1 && isNull l2
      | Seqp(l1,l2) -> isNull l1 && isNull l2
      | _ -> false
  and isNull = Fix.fix isNullF true
  
  let (|Emptyp|_|) parser = if isEmpty parser then Some(parser) else None

  let (|Nullp|_|) parser = if isNull parser then Some(parser) else None
  
  let mutableAdd (hs : HashSet<ParseSet>) item =
    hs.Add(item)
    hs
  
  let rec parseNullF parser =  (* Still need to finish. *)
    match parser with 
      | Empty       -> new HashSet<ParseSet>()
      | EpsS S      -> S
      | Epsilon     -> 
        let set = new HashSet<ParseSet>()
        mutableAdd set EpsilonS
      | Token c     -> new HashSet<ParseSet>()
      | Altp(l1,l2) -> 
        let hs : HashSet<ParseSet> = (parseNull l1)
        hs.UnionWith (parseNull l2)
        hs
      | Seqp(l1,l2) -> 
        let s = new HashSet<ParseSet>();
        let s1,s2 = (parseNull l1, parseNull l2)
        for p1 in s1 do
          for p2 in s2 do
            s.Add(Cons(p1,p2))
        printfn "%A" s
        s //Set.union (parseNull l1) (parseNull l2)
      | _ -> failwith "ParseNull Error, type not caught"
  and parseNull = Fix.fix parseNullF (new HashSet<ParseSet>())
  (* Incorrect, need to handle Seqp *)

  let printParser parser = 
    let rec printIt parser = 
      match parser with
        | Empty       -> printf "Empty"
        | Epsilon     -> printf "Epsilon"
        | Token c     -> printf "Token %c" c
        | Altp(l1,l2) ->
          printf "Alt("
          printIt l1
          printf ", "
          printIt l2
          printf ")"
        | Seqp(l1,l2) -> 
          printf "Seq("
          printIt l1
          printf ", "
          printIt l2
          printf ")"
        | _ -> printf "%A" parser
    printIt parser
    printf "\n"
    true

  let rec compactF (parser : Parser) = 
    printfn "%A" parser
    match parser with
      | Empty       -> parser
      | Epsilon     -> parser
      | Emptyp  p   -> Empty
      | Nullp  p    -> EpsS (parseNull p)
      | Token c     -> parser
      | Altp(l1,l2) -> 
        if isEmpty l1 then compact l2
        else if isEmpty l2 then compact l1
        else
          let l1c, l2c = (compact l1, compact l2)
          Alt(lazy(l1c), lazy(l2c))
      | Seqp(l1,l2) -> 
        if (isEmpty l1 || isEmpty l2) then Empty
        else if isEpsilon l1 then compact l2
        else if isEpsilon l2 then compact l1
        else 
          let l1c, l2c = (compact l1, compact l2)
          Seq (lazy(l1c), lazy(l2c))
      | _ -> 
        printfn "Compact, %A Found" parser
        parser
  
  and compact = memoize compactF (* Fix point this *)
  
  let alt2 = memoize (fun l1 l2 -> compact(Alt(lazy(l1), lazy(l2)))) (* Is this really memoized? *)
  
  let seq2 = memoize (fun l1 l2 -> compact(Seq(lazy(l1),lazy(l2))))
  
  let seq parsers = List.reduce seq2 (Epsilon::parsers)
  
  let alt parsers = List.reduce alt2 (Empty::parsers) (* Not sure if begin or end matter. *)

  let rec deriveF c parser = 
    match parser with 
      | Empty        -> Empty
      | Epsilon      -> Empty
      | Token tok    ->
        if c = tok then Epsilon
        else Empty
      | Altp(l1, l2) -> 
        let d1 = derive c l1
        let d2 = derive c l2
        alt [derive c l1; derive c l2]
      | Seqp(l1, l2) ->
        let der = seq [derive c l1; l2]
        if nullable l1 then alt [der; derive c l2]
        else der
      | _ -> parser (* Never should be hit? *)
  
  and derive = 
    memo2d deriveF

  let rec parseDeriveF c parser =
    match parser with
      | Empty     -> Empty
      | Epsilon   -> Epsilon
      | EpsS _    -> Empty
      | Token tok ->
        if c = tok then 
          let set = HashSet<ParseSet>();
          set.Add(TokenS(c))
          EpsS (set)
        else Empty
      | Altp(l1, l2) -> alt [parseDerive c l1; parseDerive c l2]
      | Seqp(l1, l2) ->
        let der = seq [parseDerive c l1; l2]  (* TODO: Make sure this line is right ifNullable l1 or parser *)
        if nullable l1 then alt [seq [EpsS (parseNull l1); parseDerive c l2]; der]
        else der
  
  and parseDerive = 
    memo2d parseDeriveF
  
  let parses parser tokens = 
    let rec partialParse parser tokens = 
      match tokens with 
        | []    -> nullable parser
        | c::cs -> partialParse (derive c parser) cs
    partialParse parser tokens   

  let rec parse p s =
    match s with
      | []    -> parseNull p
      | c::cs -> parse (parseDerive c p) cs   (* Use parse-derive *)

  (* DEBUGGING *)
  
  let rec sizeF parser = 
    match parser with 
      | Empty      -> 1
      | Epsilon    -> 1
      | Token c      -> 1
      | Altp(l1,l2) -> 1 + size l1 + size l2
      | Seqp(l1,l2) -> 1 + size l1 + size l2
      | _ -> 0
  and size = Fix.fix sizeF 0

  let rec lit charArray =
    match charArray with
      | []    -> []
      | c::cs -> (Token c)::(lit cs)
  
  let parses_str parser str = 
    let chars = String.explode str
    let rec partialParse parser chars = 
      match chars with 
        | []    -> nullable parser
        | c::cs -> partialParse (derive c parser) cs
    partialParse parser chars   

  (* TEST *)
  let simple = Seq (lazy(Token('x')), lazy(Epsilon))
  let lit_xy = Seq( lazy(Seq( lazy(Token('x')), lazy(Token('y') ) )), lazy(Epsilon))
  
  let literal litr = 
    let chararray = String.explode litr
    seq (lit chararray)
  
  let string_lits literal = 
    let chararray = String.explode literal
    lit chararray
  
  let mini_java =
    let space = Token ' '
    let alphabet = alt (string_lits "abcdefghijklmnopqrstuvwxyz")
    let capAlpha = alt (string_lits "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
    let optChar = alt ([alphabet; capAlpha; Epsilon])
    let prims = alt ([literal "void"; literal "boolean";  literal "byte"; literal "char"; literal "short"; literal "int"; literal "float"; literal "double"; literal "long"])
    let jClass = seq [capAlpha; optChar; optChar; optChar; optChar; optChar; optChar; optChar;]
    //let ADTyp = seq [literal "<"; 'a'; literal ">"]
    let access = alt ([literal "private"; literal "public"; literal "abstract"])
    let retTyp = alt ([jClass; prims])
    let funct = seq [alphabet; optChar; optChar; optChar; optChar; optChar; optChar; optChar; optChar; optChar]; //Only three letters right now.
    let parens = literal "()"
    let mini_java = seq [access; space; retTyp; space; funct; parens]
    mini_java
  
  let main literal =
    let str = literal
    let chararray = String.explode str
    let lits = lit chararray
    let seq_xy = seq lits
    let alt_xy = alt lits
    seq_xy
  let language = main "hi"  
  (* Parser.parses Parser.mini_java Parser.language *)