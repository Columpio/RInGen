// Signature file for parser generated by fsyacc
module Parser
type token = 
  | EOF
  | LPAREN
  | RPAREN
  | QUOTE
  | MATCH
  | COMMENT
  | Sym of (string)
  | Str of (string)
  | Int of (int)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_QUOTE
    | TOKEN_MATCH
    | TOKEN_COMMENT
    | TOKEN_Sym
    | TOKEN_Str
    | TOKEN_Int
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_expr
    | NONTERM_pattern
    | NONTERM_match_case
    | NONTERM_match_case_list
    | NONTERM_list
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (ParseExpression) 
