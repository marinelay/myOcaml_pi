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
%token COMMA
%token IMPLY
%token NOTEQ

%token EXIST, FORALL
%token DOT


%left PLUS MINUS
%left STAR SLASH
%left AND_S
%left IMPLY

%left SEMI

%left FOR


%start program
%type <Calc.program> program
%%

program:
  start EOF { $1 }
  ;

start:
  | AT bexp AT bexp ID LPAREN inits RPAREN LCURLY stmt RCURLY { Calc.FUNC_START ( $2, $7, $10, $4) }

stmt:
  | stmt stmt { Calc.SEQ ($1, $2) }
  | assign SEMI { $1 }
  | IF LPAREN exp RPAREN LCURLY stmt RCURLY ELSE LCURLY stmt RCURLY  { Calc.IF ($3, $6, $10) }
  | IF LPAREN exp RPAREN LCURLY stmt RCURLY { Calc.IF ($3, $6, Calc.UNIT) }
  | LPAREN RPAREN { Calc.UNIT }
  | AT bexp FOR LPAREN assign SEMI exp SEMI assign RPAREN LCURLY stmt RCURLY { Calc.FOR ($2, $5, $7, $9, $12) }
  | RETURN bool SEMI { Calc.RETURN $2 }
  | RETURN ID LPAREN exps RPAREN SEMI { Calc.RETURN_FUNC ($4) }

exps:
  | exps COMMA exp { $1@[$3] } 
  | exp {[$1]}

exp:
  | NUM { Calc.INT $1 }
  | bexp { $1 }
  | ID { Calc.VAR $1 }
  | ID LBLOCK exp RBLOCK { Calc.ARR ($1, $3)}
  | LPAREN exp RPAREN { $2 }
  | exp PLUS exp { Calc.ADD ($1, $3) }

bool:
  | TRUE { Calc.TRUE }
  | FALSE { Calc.FALSE }

var_typ:
  | { "" }
  | INT { ("int") }

typ:
  | INT { ( "int" ) }

assign:
  | var_typ ID COLEQ exp { Calc.ASSIGN ($2, $4) }
  | var_typ ID LBLOCK exp RBLOCK COLEQ exp { Calc.ASSIGN_ARR ($2, $4, $7) }

inits:
  | inits init { $1@[$2] }
  | init { [$1] }

init:
  | typ ID { Calc.VAR( $2 ) }
  | typ ID LBLOCK RBLOCK { Calc.ARR( $2, Calc.UNIT ) }

pre_conds:
  | pre_conds AND_S pre_cond { $1@[$3] }
  | pre_cond { [$1] }
  

pre_cond:
  | bexp { $1 }


id_list:
  | ID { [$1] }
  | id_list COMMA ID { $1@[$3] }

bexp :
  | bool { $1 }
  | LPAREN bexp RPAREN {$2}
  | EXIST id_list DOT LPAREN bexp RPAREN { Calc.EXIST($2, $5) }
  | FORALL id_list DOT LPAREN bexp RPAREN { Calc.FORALL($2, $5) }
  | bexp AND_S bexp { Calc.AND_EXP ($1, $3)}
  | bexp IMPLY bexp { Calc.IMPLY ($1, $3)}
  | exp EQUAL exp { Calc.EQUAL ($1, $3) }
  | exp NOTEQ exp { Calc.NOTEQUAL ($1, $3) }
  | exp LT exp { Calc.LT ($1, $3) }
  | exp LE exp { Calc.LE ($1, $3) }
  | exp GT exp { Calc.GT ($1, $3) }
  | exp GE exp { Calc.GE ($1, $3) }
  

%%

let parser_error s = print_endline s
