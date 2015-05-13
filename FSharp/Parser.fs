open System
open System.Text
open System.Collections.Generic
  
module String =
  let explode (s:string) = [for c in s -> c]

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
          running := false
          Cache.Clear()
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

module Memoize = 
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
        if cache2.ContainsKey(c) then 
          cache2.[c]
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

module Parser =
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
    | Z of Lazy<Parser>
    | Refr of Ref<Parser>

  (* Active Pattern Matchers *)
  let (|Seqp|_|) parser =
    match parser with
      | Seq(l1,l2) -> Some(l1.Force(), l2.Force())
      | _          -> None

  let (|Altp|_|) parser =
    match parser with
      | Alt(l1,l2) -> Some(l1.Force(), l2.Force())
      | _          -> None
  
  (* Checks if a Parser is nullable. Uses Least Fixed Point. *)
  let rec nullableF parser =
    match parser with
      | Empty       -> false
      | Epsilon     -> true
      | EpsS _      -> true
      | Token c     -> false
      | Altp(l1,l2) -> nullable l1 || nullable l2
      | Seqp(l1,l2) -> nullable l1 && nullable l2
      | Refr L1     -> nullable (!L1)
      | Z l         -> nullable (l.Force())
      | _           -> true
  and nullable = Fix.fix nullableF false

  let (|Nullablep|_|) parser = if nullable parser then Some(parser) else None 

  (* Generates a parse forest from the given parser. Uses fix point algorithm *)
  let rec parseNullF parser = 
    match parser with 
      | Empty       -> new HashSet<ParseSet>()
      | EpsS S      -> S
      | Epsilon     -> 
        printfn "PARSER %A" parser
        let set = new HashSet<ParseSet>()
        set.Add(EpsilonS) |> ignore
        set
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
            s.Add(Cons(p1,p2)) |> ignore
        s
      | Z l1   -> parseNull (l1.Force())
      | Refr l -> parseNull (!l)
      | _ -> failwith "ParseNull Error, type not caught"
  and parseNull = Fix.fix parseNullF (new HashSet<ParseSet>())

  (* Checks if a parser reduces to the empty parser. Uses fix point algorithm. *)
  let rec isEmptyF parser =
    match parser with
      | Empty       -> true
      | Epsilon     -> false
      | Token c     -> false
      | Altp(l1,l2) -> isEmpty l1 && isEmpty l2
      | Seqp(l1,l2) -> isEmpty l1 || isEmpty l2
      | Z l         -> isEmpty (l.Force())
      | Refr l      -> isEmpty (!l)
      | _           -> false
  and isEmpty = Fix.fix isEmptyF false
  
  (* Checks if a parser is the empty string. Uses fix point algorithm. *)
  let rec isNullF parser = 
    match parser with
      | Empty       -> false
      | Epsilon     -> true
      | Token _     -> false
      | Altp(l1,l2) -> isNull l1 && isNull l2
      | Seqp(l1,l2) -> isNull l1 && isNull l2
      | Refr l      -> isNull (!l)
      | Z l         -> isNull (l.Force())
      | _           -> false
  and isNull = Fix.fix isNullF false
  
  (* Active pattern matchers for isEmpty and isNull *)
  let (|Emptyp|_|) parser = if isEmpty parser then Some(parser) else None

  let (|Nullp|_|) parser = 
    if isNull parser && (parseNull parser).Count = 1 then Some(parser) else None
  
  (* Memoized functions to create parsers. *)
  let alt2 = Memoize.memoize (fun l1 l2 -> Alt(lazy(l1), lazy(l2))) 
  
  let seq2 = Memoize.memoize (fun l1 l2 -> Seq(lazy(l1), lazy(l2)))
  
  let rec seq parsers = 
    match parsers with
      | []    -> Epsilon
      | p::[] -> p
      | p::ps -> seq2 p (seq ps)
  
  let rec alt parsers = 
    match parsers with
      | []    -> Empty
      | p::[] -> p
      | p::ps -> alt2 p (alt ps)

  (* A memoized compact function. Applies algebraic reductions to a parser. *)
  let rec compactF (parser : Parser) = 
    match parser with
      | Empty       -> parser
      | Epsilon     -> parser
      | Emptyp  p   -> Empty
      | Nullp   p   -> EpsS (parseNull p)
      | Token c     -> parser
      | Altp(l1,l2) -> 
        if      isEmpty l1 then compact l2 
        else if isEmpty l2 then compact l1
        else alt [compact l1; compact l2]
      | Seqp(l1,l2) -> 
        if (isEmpty l1 || isEmpty l2) then Empty
        else if isNull l1 then compact l2
        else if isNull l2 then compact l1
        else seq [compact l1; compact l2]
      | Refr l -> parser
      | Z l    -> parser
      | _      -> parser
  and compact = Memoize.memoize compactF

  (* A memoized derivation used for language recognition. *)
  let rec deriveF c parser = 
    match parser with 
      | Empty        -> Empty
      | Epsilon      -> Empty
      | Token tok    -> if c = tok then Epsilon else Empty
      | Altp(l1, l2) -> alt [derive c l1; derive c l2]
      | Seqp(l1, l2) ->
        let der = seq [Z (lazy(derive c l1)); l2]
        if nullable l1 then alt [der; derive c l2]
        else der
      | Refr l -> derive c (!l)
      | EpsS _ -> parser 
      | _      -> failwith "Invalid parse. [function->parse]" (* Never should be hit. *)
  and derive = Memoize.memo2d deriveF

  (* A memoized parse derivation used to create parse forests. *)
  let rec parseDeriveF c parser =
    match parser with
      | Empty     -> Empty
      | Epsilon   -> Empty
      | EpsS _    -> Empty
      | Token tok ->
        if c = tok then 
          let set = HashSet<ParseSet>();
          set.Add(TokenS(c)) |> ignore
          EpsS (set)
        else Empty
      | Altp(l1, l2) -> 
        alt [parseDerive c l1; parseDerive c l2]
      | Seqp(l1, l2) ->
        let der = seq [Z (lazy(parseDerive c l1)); l2]  (* TODO: Make sure this line is right ifNullable l1 or parser *)
        if nullable l1 then 
          alt [seq [EpsS (parseNull l1); parseDerive c l2]; der]
        else der
      | Z l1      -> parseDerive c (l1.Force())
      | Refr l    -> parseDerive c (!l)
      | _ -> failwith "Invalid parse. [function->parseDerive]" (* Invalid match, shouldn't happen *)
  and parseDerive = Memoize.memo2d parseDeriveF
  
  (* A language recognition function. *)
  let rec parses p toks = 
    match toks with 
      | []    -> nullable p
      | c::cs -> parses (compact(derive c p)) cs

  (* Generate parse forest for given parser and tokens. *)
  let rec parse p s =
    match s with
      | []    -> parseNull p
      | c::cs -> parse (compact(parseDerive c p)) cs

  (* DEBUG *)
  (* Functions used for Debugging: *)
  let printParser parser = 
    let rec printIt parser = 
      match parser with
        | Empty       -> printf "Empty"
        | Epsilon     -> printf "Epsilon"
        | EpsS s      -> printf "EpsS(%A)" s
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
        | Refr l     -> printf "Ref()"
        | Z l        -> printf "Z" 
        | _ -> printf "%A" parser
    printIt parser
    printf "\n"
    ()

  (* Give a rough estimate of the size of the current parser. Uses fix point algorithm. *)
  let rec sizeF parser = 
    match parser with 
      | Empty       -> 1
      | Epsilon     -> 1
      | EpsS _      -> 1
      | Token c     -> 1
      | Altp(l1,l2) -> 1 + size l1 + size l2
      | Seqp(l1,l2) -> 1 + size l1 + size l2
      | Refr l      -> 1
      | _           -> 0
  and size = Fix.fix sizeF 0
 

  (* Generate token literals for given character array input. *)
  let rec lit charArray =
    match charArray with
      | []    -> []
      | c::cs -> (Token c)::(lit cs)
  
  (* Check is a language is capable of parsing a given string input. *)
  let parses_str parser str = 
    let chars = String.explode str
    let rec partialParse parser chars = 
      match chars with 
        | []    -> nullable parser
        | c::cs -> partialParse (compact(derive c parser)) cs
    partialParse parser chars   

  (* Sample languages used for testing the parser. *)
  let simple = Seq (lazy(Token('x')), lazy(Epsilon))
  let lit_xy = Seq(lazy(Seq( lazy(Token('x')), lazy(Token('y') ) )), lazy(Epsilon))
  
  (* Generate a literal from given input string. *)
  let literal litr = 
    let chararray = String.explode litr
    seq (lit chararray)
  
  (* Generate token literals from string input. *)
  let string_lits literal = 
    let chararray = String.explode literal
    lit chararray

  (* Gets a tree from a parse forest. *)
  let getTree (trees : HashSet<ParseSet>) num =
    let treeList = trees |> Seq.toList
    let rec loop treeList num =   
      match treeList with
        | []    -> failwith "Index out of bounds"
        | t::ts -> if num = 0 then t else loop ts (num-1)
    loop treeList num 

  (* Displays a clean printout of a tree. *)
  let printTree trees num =
    let (tree : ParseSet) = getTree trees num
    let rec depthPrint num = 
      match num with 
        | 0 -> ()
        | _ -> printf "\t"
               depthPrint (num-1)
    let rec printIt tree depth = 
      match tree with
        | TokenS t    -> 
          depthPrint (depth)
          printfn "%A" tree
        | Cons(t1,t2) -> 
          depthPrint depth
          if depth = 0 then printfn "S" else printfn "NT"
          printIt t1 (depth+1)
          printIt t2 (depth+1)
        | _ -> printf "()"
          
    printIt tree 0
      
  (* Parser.parse Parser.rlist ['r';'r';'r'];; *)
  let rlist =   (* rlist -> rlist+'r' | 'r'  *)
    let rl = ref Empty
    rl := Alt(lazy(Seq(lazy(Refr rl), lazy(Token 'r'))), lazy(Token 'r'))
    !rl
  
  (* xylist -> 'xy' xylist | 'xy' *)
  let xylist = 
    let xy  = literal "xy"
    let xyl = ref Empty
    xyl := Alt(lazy(Seq(lazy(xy), lazy(Refr xyl))), lazy(xy))
    !xyl

  (* N -> N + N | 'N' *)
  let nMath =
    let nl = ref Empty
    let op = alt [Token '+'; Token '-'; Token '/'; Token '*']
    nl := Alt(lazy(Seq(lazy(Seq(lazy(Refr nl),lazy(op))), lazy(Refr nl))), lazy(Token 'N'))
    !nl

  (* Basic order of operations. *)
  let bMath =
    let E  = ref Empty
    let T  = ref Empty
    let F  = ref Empty
    let G  = ref Empty
    let nums =  alt (lit (String.explode "0123456789"))
    E := alt [seq [Refr E; Token '+'; Refr T]; Refr T]
    T := alt [seq [Refr T; Token '*'; Refr F]; Refr F]
    F := alt [seq [Refr G; Token '^'; Refr F]; Refr G]
    G := alt [nums; seq [Token '('; Refr E; Token ')']]
    !E

  let main () =
    let input = ['4';'+';'2';'*';'3']
    let forest = parse bMath input
    printTree forest 0

Parser.main ()