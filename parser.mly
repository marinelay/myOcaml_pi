%token <float> NUM
%token <string> ID
%token TRUE FALSE
%token PLUS MINUS STAR SLASH
%token LPAREN RPAREN
%token LCURLY RCURLY
%token LBLOCK RBLOCK
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
%token INT

%left PLUS MINUS
%left STAR SLASH
%left SEMI

%start file
%type <newPi.file> file
%%

file:
  exp EOF { $1 }
  ;

exp:
    LPAREN RPAREN { newPi.UNIT }
  | NUM { newPi.NUM $1 }
  | TRUE { newPi.TRUE }
  | FALSE { newPi.FALSE }
  | ID { newPi.VAR $1 }
  | LPAREN exp RPAREN { $2 }
  | exp PLUS exp { newPi.ADD ($1, $3) }
  | exp MINUS exp { newPi.SUB ($1, $3) }
  | exp STAR exp { newPi.MUL ($1, $3) }
  | exp SLASH exp { newPi.DIV ($1, $3) }
  | exp EQEQ exp { newPi.EQ ($1, $3) }
  | exp LT exp { newPi.LT ($1, $3) }
  | exp LE exp { newPi.LE ($1, $3) }
  | exp GT exp { newPi.GT ($1, $3) }
  | exp GE exp { newPi.GE ($1, $3) }
  | INT ID COLEQ exp SEMI exp { newPi.ASSIGN ($2, $4, $6) }
  | ID COLEQ exp SEMI exp { newPi.ASSIGN ($1, $3, $5) }
  | NOT exp { newPi.NOT ($2) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY ELSE LCURLY exp RCURLY  { newPi.IF ($3, $6, $10) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY { newPi.IF ($3, $6, newPi.UNIT) }
  | ID LPAREN exp RPAREN exp { newPi.FUNC_START ($3, $5) }
  | exp SEMI exp { newPi.SEQ ($1, $3) }

%%

let parser_error s = print_endline s
