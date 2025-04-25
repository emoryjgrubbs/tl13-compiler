%{
#include <stdio.h>
#include "tl13.h"
int yylex(void);
int yyerror(char *);

extern int yylineno;

program *buildP(declaration *decls, statement *smts);
declaration *buildD(int line, char *id, type type, declaration *next);
statement *appendSmt(statement *ptr, statement *next);
statement *buildS(smtType type, void *smt);
assignment *buildA(int line, asnType type, char* id, exp* exp);
ifState *buildI(int line, exp *exp, statement *thenC, statement *elseC);
whileState *buildWh(int line, exp *exp, statement *doC);
writeState *buildWr(int line, exp *exp);
exp *buildE(sExp *sExpOne, expOp op, sExp *sExpTwo);
sExp *buildSE(term *termOne, sExpOp op, term *termTwo);
term *buildT(fact *factOne, termOp op, fact *factTwo);
fact *buildF(factType type, void *value);

%}

%locations

// Symbols.
%union { 
    char        *sval; 
    int         ival;
    program     *pPtr;
    declaration *dPtr;
    type        type;
    statement   *sPtr;
    assignment  *aPtr; 
    ifState     *iPtr;
    whileState  *whPtr;
    writeState  *wrPtr;
    exp         *ePtr;
    sExp        *sEPtr;
    term        *tPtr;
    fact        *fPtr;
};

%token <sval> NUMBER
%token <sval> BOOLEAN
%token <sval> IDENT
%token LP
%token RP
%token ASGN
%token SC
%token MULT
%token DIV
%token MOD
%token PLUS
%token DASH
%token EQUAL
%token NEQUAL
%token LT
%token GT
%token LTE
%token GTE
%token IF
%token THEN
%token ELSE
%token BGN
%token END
%token WHILE
%token DO
%token PROGRAM
%token VAR
%token AS
%token INT
%token BOOL
%token WRITEINT
%token READINT

%start Program

%type <pPtr> Program
%type <dPtr> Declarations
%type <type> Type
%type <sPtr> StatementSequence Statement ElseClause
%type <aPtr> Assignment
%type <iPtr> IfStatement
%type <whPtr> WhileStatement
%type <wrPtr> WriteInt
%type <ePtr> Expression
%type <sEPtr> SimpleExpression
%type <tPtr> Term
%type <fPtr> Factor

%%
Program:
    PROGRAM Declarations BGN StatementSequence END { $$ = buildP($2, $4); genProg($$); }
    ;
Declarations:
    VAR IDENT AS Type SC Declarations   { $$ = buildD((@1.first_line), $2, $4, $6); }
    | /* epsilon */                     { $$ = NULL; }
    ;
Type:
    INT     { $$ = INT_TYPE; }
    | BOOL  { $$ = BOOL_TYPE; }
    ;
StatementSequence:
    Statement SC StatementSequence  { $$ = appendSmt($1, $3); } // modify $1 statement struct to have $3 as *next
    | /* epsilon */                 { $$ = NULL; }
    ;
Statement:
    Assignment          { $$ = buildS(ASN_SMT, $1); }
    | IfStatement       { $$ = buildS(IF_SMT, $1); }
    | WhileStatement    { $$ = buildS(WHILE_SMT, $1); }
    | WriteInt          { $$ = buildS(WRITE_SMT, $1); }
    ;
Assignment:
    IDENT ASGN Expression   { $$ = buildA(@1.first_line, EXP_ASN, $1, $3); }
    | IDENT ASGN READINT    { $$ = buildA(@1.first_line, READ_ASN, $1, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
IfStatement:
    IF Expression THEN StatementSequence ElseClause END { $$ = buildI(@1.first_line, $2, $4, $5); }
    ;
ElseClause:
    ELSE StatementSequence  { $$ = $2; }
    | /* epsilon */         { $$ = NULL; }
    ;
WhileStatement:
    WHILE Expression DO StatementSequence END   { $$ = buildWh(@1.first_line, $2, $4); }
    ;
WriteInt:
    WRITEINT Expression { $$ = buildWr(@1.first_line, $2); }
    ;
Expression:
    SimpleExpression EQUAL SimpleExpression     { $$ = buildE($1, EQUAL_OP, $3); }
    | SimpleExpression NEQUAL SimpleExpression  { $$ = buildE($1, NEQUAL_OP, $3); }
    | SimpleExpression LT SimpleExpression      { $$ = buildE($1, LT_OP, $3); }
    | SimpleExpression GT SimpleExpression      { $$ = buildE($1, GT_OP, $3); }
    | SimpleExpression LTE SimpleExpression     { $$ = buildE($1, LTE_OP, $3); }
    | SimpleExpression GTE SimpleExpression     { $$ = buildE($1, GTE_OP, $3); }
    | SimpleExpression                          { $$ = buildE($1, NO_EXP_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
SimpleExpression:
    Term PLUS Term      { $$ = buildSE($1, PLUS_OP, $3); }
    | Term DASH Term    { $$ = buildSE($1, MINUS_OP, $3); }
    | Term              { $$ = buildSE($1, NO_SEXP_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
Term:
    Factor MULT Factor  { $$ = buildT($1, MULT_OP, $3); }
    | Factor DIV Factor { $$ = buildT($1, DIV_OP, $3); }
    | Factor MOD Factor { $$ = buildT($1, MOD_OP, $3); }
    | Factor            { $$ = buildT($1, NO_TERM_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
Factor:
    IDENT               { $$ = buildF(ID_FACT, $1); }
    | NUMBER            { $$ = buildF(NUM_FACT, $1); }
    | BOOLEAN           { $$ = buildF(BOOL_FACT, $1); }
    | LP Expression RP  { $$ = buildF(SUB_EXP_FACT, $2); }
    ;
%%

program *buildP(declaration *decls, statement *smts) {
    program *ptr;
	if ((ptr = malloc(sizeof(program))) == NULL) {
		yyerror("out of memory");
	}
    ptr->decls = decls;
    ptr->smts = smts;
    return ptr;
}

declaration *buildD(int line, char *id, type type, declaration *next) {
    declaration *ptr;
	if ((ptr = malloc(sizeof(declaration))) == NULL) {
		yyerror("out of memory");
	}
    ptr->line = line;
    ptr->id = id;
    ptr->type = type;
    ptr->next = next;
    return ptr;
}

statement *appendSmt(statement *ptr, statement *next) {
    ptr->next = next;
    return ptr;
}
statement *buildS(smtType type, void *smt) {
    statement *ptr;
	if ((ptr = malloc(sizeof(statement))) == NULL) {
		yyerror("out of memory");
	}
    ptr->type = type;
    switch (type) {
        case ASN_SMT:
            ptr->smt.asn = smt;
            break;
        case IF_SMT:
            ptr->smt.ifS = smt;
            break;
        case WHILE_SMT:
            ptr->smt.whileS = smt;
            break;
        case WRITE_SMT:
            ptr->smt.write = smt;
            break;
    }
    return ptr;
}

assignment *buildA(int line, asnType type, char* id, exp* exp) {
    assignment *ptr;
	if ((ptr = malloc(sizeof(assignment))) == NULL) {
		yyerror("out of memory");
	}
    ptr->line = line;
    ptr->type = type;
    ptr->id = id;
    ptr->exp = exp;
    return ptr;
}

ifState *buildI(int line, exp *exp, statement *thenC, statement *elseC) {
    ifState *ptr;
	if ((ptr = malloc(sizeof(ifState))) == NULL) {
		yyerror("out of memory");
	}
    ptr->line = line;
    ptr->exp = exp;
    ptr->thenC = thenC;
    ptr->elseC = elseC;
    return ptr;
}

whileState *buildWh(int line, exp *exp, statement *doC) {
    whileState *ptr;
	if ((ptr = malloc(sizeof(whileState))) == NULL) {
		yyerror("out of memory");
	}
    ptr->line = line;
    ptr->exp = exp;
    ptr->doC = doC;
    return ptr;
}

writeState *buildWr(int line, exp *exp) {
    writeState *ptr;
	if ((ptr = malloc(sizeof(writeState))) == NULL) {
		yyerror("out of memory");
	}
    ptr->line = line;
    ptr->exp = exp;
    return ptr;
}

exp *buildE(sExp *sExpOne, expOp op, sExp *sExpTwo) {
    exp *ptr;
	if ((ptr = malloc(sizeof(exp))) == NULL) {
		yyerror("out of memory");
	}
    ptr->sExpOne = sExpOne;
    ptr->op = op;
    ptr->sExpTwo = sExpTwo;
    return ptr;
}

sExp *buildSE(term *termOne, sExpOp op, term *termTwo) {
    sExp *ptr;
	if ((ptr = malloc(sizeof(sExp))) == NULL) {
		yyerror("out of memory");
	}
    ptr->termOne = termOne;
    ptr->op = op;
    ptr->termTwo = termTwo;
    return ptr;
}

term *buildT(fact *factOne, termOp op, fact *factTwo) {
    term *ptr;
	if ((ptr = malloc(sizeof(term))) == NULL) {
		yyerror("out of memory");
	}
    ptr->factOne = factOne;
    ptr->op = op;
    ptr->factTwo = factTwo;
    return ptr;
}

fact *buildF(factType type, void *value) {
    fact *ptr;
	if ((ptr = malloc(sizeof(fact))) == NULL) {
		yyerror("out of memory");
	}
    ptr->type = type;
    switch (type) {
        case ID_FACT:  
            ptr->value.id = value;
            break;
        case NUM_FACT:
            // make value not void *
            char *strVal = value;

            int numVal = 0;
            int i = 0;

            // while the character isn't null
            while (strVal[i] != '\0') {
                // val =  shifted val  + value of new char
                numVal = (10 * numVal) + (strVal[i] - '0');
                i++;
            }

            ptr->value.num = numVal;
            break;
        case BOOL_FACT:
            if (value == "true") {
                ptr->value.boole = TRUE_BOOL;
            }
            else {
                ptr->value.boole = FALSE_BOOL;
            }
            break;
        case SUB_EXP_FACT:
            ptr->value.subExp = value;
            break;
    }
    return ptr;
}

int yyerror(char *s) {
  printf("yyerror : %s\n",s);
}
int main(void) {
  yyparse();
}
int yywrap() {
}
