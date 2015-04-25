# Derivative Combinator

F# and OCaml implementations of Matt Mights _Parsing with Derivatives_.

__Note:__
- Currently in development phases still
- Test folder houses an attempt to apply the combinator to a small programming
language.

### Functions
Functions used in parsing.

| Function  | Purpose |
|-----------|---------|
| memoize   | Allows porgram to terminate by using memory. |
| force     | Returns the two parsed languages (for Seq and Alt) |
| nullable  | Whether the parser can be reduced to the empty string |
| isEmpty   | Is the parser Empty |
| isEpsilon | Is the parser Epsilon |
| isNull    | Is the parser just the empty string |
| compact   | Algebraic compactions on the parser language |
| alt       | Create a union language |
| seq       | Create a concatenated language |
| derive    | Derive a parser with respect to a character |
| size      | Return the size of a parser |
| parses    | Whether a parser recognized a given input |
| parse     | Return a set of possible parses |
