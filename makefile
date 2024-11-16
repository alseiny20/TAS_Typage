
run_tests_ast:
	ocamlc -o testAst ast.ml structure.ml tests/astTests.ml && ./testAst

run_ast:
	ocamlc -o ast structure.ml ast.ml  && ./ast
	
run_type:
	ocamlc -o structure.ml type ast.ml type.ml && ./type

run_tests_type:
	ocamlc -o typeTest structure.ml  ast.ml type.ml tests/typeTests.ml  && ./typeTest


clean:
	rm -f *.cmi &&  rm -f *.cmo &&   rm -f ./tests/*.cmi && rm -f ./tests/*.cmo