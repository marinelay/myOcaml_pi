#load "str.cma"

TARGET = run

all: $(TARGET)

$(TARGET):  util.cmo lexer.cmo parser.cmo z3_translator.cmo calc.cmo simplify.cmo solve.cmo main.cmo
	ocamlc -o $@ $^




util.cmo : util.ml
	ocamlc -c util.ml

z3_translator.cmo : z3_translator.ml
	ocamlfind ocamlc -c -linkpkg -package str -package z3 -o -thread z3_translator.ml

calc.cmo : calc.ml
	ocamlc -c  calc.ml

simplify.cmo : simplify.ml
	ocamlfind ocamlc -linkpkg -package z3 -c simplify.ml

solve.cmo : solve.ml
	ocamlfind ocamlc -linkpkg -package z3 -c solve.ml



parser.ml: parser.mly calc.cmo
	ocamlyacc parser.mly

parser.mli: parser.mly
	ocamlyacc parser.mly

parser.cmi: parser.mli
	ocamlc -c parser.mli

parser.cmo: parser.ml parser.cmi
	ocamlc -c parser.ml

main.cmo : calc.cmo main.ml
	ocamlfind ocamlc -linkpkg -package z3 -c main.ml

lexer.cmo: lexer.ml
	ocamlc -c lexer.ml

lexer.ml: lexer.mll parser.cmo
	ocamllex lexer.mll

clean:
	rm -f *.cmx *.cmi parser.mli parser.ml lexer.ml run *.o *.cmo