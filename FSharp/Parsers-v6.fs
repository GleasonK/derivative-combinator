open System
open System.Text
open System.Collections.Generic
  
module String =
  let explode (s:string) =
    [for c in s -> c]


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
  
  type Parser = 
    | Empty
    | Epsilon
    | Lit of char
    | Alt of Lazy<Parser> * Lazy<Parser>
    | Seq of Lazy<Parser> * Lazy<Parser>
  
  let force l =
    match l with 
      | Alt(l1,l2) -> (l1.Force(), l2.Force())
      | Seq(l1,l2) -> (l1.Force(), l2.Force())
      | _ -> failwith "Not a forceable lazy value."
  
  let rec nullable parser = 
    match parser with
      | Empty      -> false
      | Epsilon    -> true
      | Lit c      -> false
      | Alt(l1,l2) -> 
        let l1f, l2f = force parser
        nullable l1f || nullable l2f
      | Seq(l1,l2) -> 
        let l1f, l2f = force parser
        nullable l1f && nullable l2f
  
  let isEmpty parser =
    match parser with
      | Empty -> true
      | _     -> false
  
  let isEpsilon parser =
    match parser with
      | Epsilon -> true
      | _       -> false 
  
  let rec compactF (parser : Parser) = 
    match parser with
      | Empty      -> 
        printfn "EMPTY COMPACT"
        parser
      | Epsilon    -> 
        printfn "EPSILON COMPACT"
        parser
      | Lit c      -> 
        printfn "LIT COMPACT"
        parser
      | Alt(l1,l2) -> 
        let l1f, l2f = force parser
        if (isEmpty l1f) then compact l2f
        else if (isEmpty l2f) then compact l1f
        else
          printfn "ALT COMPACT"
          let l1c, l2c = (compact l1f, compact l2f)
          Alt(lazy(l1c), lazy(l2c))
      | Seq(l1,l2) -> 
        let l1f, l2f = force parser
        if (isEmpty l1f || isEmpty l2f) then Empty
        else if (isEpsilon l1f) then compact l2f
        else if (isEpsilon l2f) then compact l1f
        else 
          let l1c, l2c = (compact l1f, compact l2f)
          printfn "SEQ COMPACT"
          Seq (lazy(l1c), lazy(l2c))
  
  and compact = memoize compactF 
  
  and alt2 = memoize (fun l1 l2 -> compact(Alt(lazy(l1), lazy(l2)) ) )
  
  and seq2 = memoize (fun l1 l2 -> compact(Seq(lazy(l1),lazy(l2))))
  
  and seq parsers = List.reduce seq2 (parsers@[Epsilon])
  
  and alt parsers = List.reduce alt2 (parsers@[Empty]) //Not sure if begin or end matter.
  
  let rec deriveF c parser = 
    match parser with 
      | Empty      -> Empty
      | Epsilon    -> Empty
      | Lit tok    ->
         if c = tok then Epsilon
         else Empty
      | Alt(l1, l2) ->
        let l1f, l2f = force parser
        alt [derive c l1f; derive c l2f]  //MIGHT NEED LAZY DERIVE.
      | Seq(l1, l2) ->
        let l1f, l2f = force parser
        let der = seq [derive c l1f; l2f]
        if nullable l1f then alt [der; derive c l2f]
        else der
  
  and derive = 
    memo2d deriveF
  
  let rec size parser = 
    match parser with 
      | Empty      -> 1
      | Epsilon    -> 1
      | Lit c      -> 1
      | Alt(l1,l2) -> 
        let l1f, l2f = force parser
        1 + size l1f + size l2f
      | Seq(l1,l2) -> 
        let l1f, l2f = force parser
        1 + size l1f + size l2f
  
  let parses parser str = 
    let chars = String.explode str
    let rec partialParse parser chars = 
      match chars with 
        | []    -> nullable parser
        | c::cs -> partialParse (derive c parser) cs
    partialParse parser chars   
  
  (* DEBUGGING *)
  
  let rec lit charArray =
    match charArray with
      | []    -> []
      | c::cs -> (Lit c)::(lit cs)
  
  let printParser parser = 
    let rec printIt parser = 
      match parser with
        | Empty     -> printf "Empty"
        | Epsilon   -> printf "Epsilon"
        | Lit c     -> printf "Lit %c" c
        | Alt(l1,l2) ->
          let l1f, l2f = force parser
          printf "Alt("
          printIt l1f
          printf ", "
          printIt l2f
          printf ")"
        | Seq(l1,l2) -> 
          let l1f, l2f = force parser
          printf "Seq("
          printIt l1f
          printf ", "
          printIt l2f
          printf ")"
    printIt parser
    printf "\n"
    true
  
  (* TEST *)
  let simple = Seq (lazy(Lit('x')), lazy(Epsilon))
  let lit_xy = Seq( lazy(Seq( lazy(Lit('x')), lazy(Lit('y') ) )), lazy(Epsilon))
  
  let literal litr = 
    let str = litr
    let chararray = String.explode str
    seq (lit chararray)
  
  let string_lits literal = 
    let str = literal
    let chararray = String.explode str
    lit chararray
  
  let mini_java =
    let space = Lit ' '
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
  let language = main "hello World"  