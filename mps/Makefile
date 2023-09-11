# Create calculator
cal: scanner.l parser.y
	bison -d parser.y
	flex scanner.l
	cc -o $@ parser.tab.c lex.yy.c -lfl

calpp: scanner.ll parser.yy
	bison -d parser.yy
	flex scanner.ll
	g++ -o $@ parser.tab.c lex.yy.c -lfl
