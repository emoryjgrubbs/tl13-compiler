parser: tl13.tab.c tl13.tab.h lex.yy.c
	gcc tl13.c tl13.tab.c lex.yy.c

tl13.tab.c: tl13.y
	bison --defines tl13.y

lex.yy.c: tl13.l
	flex tl13.l

clean:
	rm -f a.out *.yy.c *.tab.c *.tab.h
