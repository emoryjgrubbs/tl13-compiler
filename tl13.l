%{
#include "tl13.h"
#include "tl13.tab.h"
#define YY_USER_ACTION yylloc.first_line = yylloc.last_line = yylineno;
%}

%option yylineno

%%
%.*             { /* eat inline comment */ }
[[:space:]]     { /* eat white space */}
[1-9][0-9]*|0   { 
                    yylval.sval = malloc(strlen(yytext));
                    strncpy(yylval.sval, yytext, strlen(yytext));
                    return(NUMBER);
                }
false|true      {
                    yylval.sval = malloc(strlen(yytext));
                    strncpy(yylval.sval, yytext, strlen(yytext));
                    return(BOOLEAN);
                }
[A-Z][A-Z0-9]*  {
                    yylval.sval = malloc(strlen(yytext));
                    strncpy(yylval.sval, yytext, strlen(yytext));
                    return(IDENT);
                }
\(              return(LP);
\)              return(RP);
:=              return(ASGN);
;               return(SC);
\*              return(MULT);
div             return(DIV);
mod             return(MOD);
\+              return(PLUS);
-               return(DASH);
=               return(EQUAL);
!=              return(NEQUAL);
\<              return(LT);
\>              return(GT);
\<=             return(LTE);
\>=             return(GTE);
if              return(IF);
then            return(THEN);
else            return(ELSE);
begin           return(BGN);
end             return(END);
while           return(WHILE);
do              return(DO);
program         return(PROGRAM);
var             return(VAR);
as              return(AS);
int             return(INT);
bool            return(BOOL);
writeInt        return(WRITEINT);
readInt         return(READINT);
%%
