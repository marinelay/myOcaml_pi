%token <float> NUM
%token <string> ID
%token TRUE FALSE
%token REF
%token EXCMARK
%token PLUS MINUS STAR SLASH
%token LPAREN RPAREN
%token EQEQ
%token LE
%token LT
%token GE
%token GT
%token NOT
%token IF
%token THEN
%token ELSE
%token LET
%token EQUAL
%token IN
%token COLEQ
%token LBRACK RBRACK
%token SEMI
%token EOF

%left IN
%left PLUS MINUS
%left STAR SLASH
%left EXCMARK
%left SEMI

%start file
%type <Calc.file> file
%%

file:
  exp EOF { $1 }
  ;

exp:
    LPAREN RPAREN { Calc.UNIT }
  | NUM { Calc.NUM $1 }
  | TRUE { Calc.TRUE }
  | FALSE { Calc.FALSE }
  | ID { Calc.VAR $1 }
  | LPAREN exp RPAREN { $2 }
  | exp PLUS exp { Calc.ADD ($1, $3) }
  | exp MINUS exp { Calc.SUB ($1, $3) }
  | exp STAR exp { Calc.MUL ($1, $3) }
  | exp SLASH exp { Calc.DIV ($1, $3) }
  | exp EQEQ exp { Calc.EQ ($1, $3) }
  | exp LT exp { Calc.LT ($1, $3) }
  | exp LE exp { Calc.LE ($1, $3) }
  | exp GT exp { Calc.GT ($1, $3) }
  | exp GE exp { Calc.GE ($1, $3) }
  | ID COLEQ exp SEMI exp { Calc.ASSIGN ($1, $3, $5) }
  | NOT exp { Calc.NOT ($2) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY ELSE exp  { Calc.IF ($3, $6, $9) }
  | exp LPAREN exp RPAREN { Calc.CALL_FUN ($1, $3) }
  | exp SEMI exp { Calc.SEQ ($1, $3) }

%%

let parser_error s = print_endline s
