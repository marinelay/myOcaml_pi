type token =
  | NUM of (float)
  | ID of (string)
  | TRUE
  | FALSE
  | REF
  | EXCMARK
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | LPAREN
  | RPAREN
  | EQEQ
  | LE
  | LT
  | GE
  | GT
  | NOT
  | IF
  | THEN
  | ELSE
  | LET
  | EQUAL
  | IN
  | COLEQ
  | LBRACK
  | RBRACK
  | SEMI
  | EOF

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Calc.file
