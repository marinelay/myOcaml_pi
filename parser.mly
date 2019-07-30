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
%left AND OR
%left AND_S
%left SEMI
%right AT

%nonassoc FOR
%nonassoc ELSE

%start program
%type <Calc.program> program
%%

program:
  exp EOF { $1 }
  ;

exp:
    LPAREN RPAREN { Calc.UNIT }
  | NUM { Calc.INT $1 }
  | bool { $1 }
  | ID { Calc.VAR $1 }
  | LPAREN exp RPAREN { $2 }
  | exp PLUS exp { Calc.ADD ($1, $3) }
  | compare { $1 }
  | var_typ ID COLEQ exp SEMI exp { Calc.ASSIGN ($2, $4, $6) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY ELSE LCURLY exp RCURLY exp  { Calc.IF ($3, $6, $10, $12) }
  | IF LPAREN exp RPAREN LCURLY exp RCURLY exp { Calc.IF ($3, $6, Calc.UNIT, $8) }
  | AT pre_conds AT pre_conds ID LPAREN exps RPAREN LCURLY exp RCURLY { Calc.FUNC_START ( $2, $7, $10, $4) }
  | exp SEMI exp { Calc.SEQ ($1, $3) }
  | AT pre_conds FOR LPAREN var_typ ID COLEQ exp SEMI exp SEMI ID COLEQ exp RPAREN LCURLY exp RCURLY exp { Calc.FOR ($2, $6, $8, $10, $12, $14, $17, $19) }
  | RETURN bool SEMI { Calc.RETURN $2 }

bool:
  | TRUE { Calc.TRUE }
  | FALSE { Calc.FALSE }

var_typ:
  | { "" }
  | INT { ("int") }

typ:
  | INT { ( "int" ) }

exps:
  | exps typ ID { $1@[($2, $3)] }
  | typ ID { [($1,$2)] }

pre_conds:
  | pre_conds AND_S compare { $1@[$3] }
  | compare { [$1] }

compare:
  | bool { $1 }
  | exp LT exp { Calc.LT ($1, $3) }
  | exp LE exp { Calc.LE ($1, $3) }
  | exp GT exp { Calc.GT ($1, $3) }
  | exp GE exp { Calc.GE ($1, $3) }

%%

let parser_error s = print_endline s
