%{

%}

%token <int> NUM
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
%token EQUAL
%token COLEQ
%token SEMI
%token EOF
%token INT
%token RETURN
%token AT
%token FOR
%token AND_S

%left PLUS MINUS
%left STAR SLASH
%left SEMI
%left AND OR
%left AND_S

%start program
%type <Calc.program> program
%%

program:
  exp EOF { $1 }
  ;

exp:
    LPAREN RPAREN { Calc.UNIT }
  | NUM { Calc.INT $1 }
  | TRUE { Calc.TRUE }
  | FALSE { Calc.FALSE }
  | ID { Calc.VAR $1 }
  | LPAREN exp RPAREN { $2 }
  | exp PLUS exp { Calc.ADD ($1, $3) }
  | compare { $1 }
  | typ ID COLEQ exp SEMI exp { Calc.ASSIGN ($2, $4, $6) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY ELSE LCURLY exp RCURLY exp  { Calc.IF ($3, $6, $10, $12) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY exp { Calc.IF ($3, $6, Calc.UNIT, $8) }
  | ID LPAREN exps RPAREN exp { Calc.FUNC_START ($3, $5) }
  | exp SEMI exp { Calc.SEQ ($1, $3) }
  | AT pre_conds FOR LPAREN ID COLEQ exp SEMI exp SEMI ID COLEQ exp RPAREN LCURLY exp RCURLY exp { Calc.FOR ($2, $5, $7, $9, $11, $13, $16, $18) }
  | RETURN exp { Calc.RETURN $2 }

typ:
  | INT { "int" }
  | { "int" }

exps:
  | typ ID exps { ($1,$2)::$3 }
  | typ ID { [($1,$2)] }

pre_conds:
  | compare AND_S pre_conds { $1::$3 }
  | compare { [$1] }

compare:
  | exp LT exp { Calc.LT ($1, $3) }
  | exp LE exp { Calc.LE ($1, $3) }
  | exp GT exp { Calc.GT ($1, $3) }
  | exp GE exp { Calc.GE ($1, $3) }

%%

let parser_error s = print_endline s
