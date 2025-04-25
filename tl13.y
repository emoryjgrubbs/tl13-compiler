%{
#include <stdio.h>
#include "tl13.h"
int yylex(void);
int yyerror(char *);

int line = 1;

program *buildP(declaration *decls, statement *smts);
declaration *buildD(char *id, type type, declaration *next);
statement *appendSmt(statement *ptr, statement *next);
statement *buildS(smtType type, void *smt);
assignment *buildA(asnType type, char* id, exp* exp);
ifState *buildI(exp *exp, statement *thenC, statement *elseC);
whileState *buildW(exp *exp, statement *doC);
exp *buildE(sExp *sExpOne, expOp op, sExp *sExpTwo);
sExp *buildSE(term *termOne, sExpOp op, term *termTwo);
term *buildT(fact *factOne, termOp op, fact *factTwo);
fact *buildF(factType type, void *value);

%}

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
    whileState  *wPtr;
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
%token ENDL

%start Program

%type <pPtr> Program
%type <dPtr> Declarations
%type <type> Type
%type <sPtr> StatementSequence Statement ElseClause
%type <aPtr> Assignment
%type <iPtr> IfStatement
%type <wPtr> WhileStatement
%type <ePtr> Expression WriteInt
%type <sEPtr> SimpleExpression
%type <tPtr> Term
%type <fPtr> Factor
%type <ival> PosEndL

%%
Program:
    PROGRAM PosEndL Declarations BGN PosEndL StatementSequence END PosEndL { $$ = buildP($3, $6); genProg($$); }
    ;
Declarations:
    VAR PosEndL IDENT PosEndL AS PosEndL Type SC PosEndL Declarations   { $$ = buildD($3, $7, $10); }
    | /* epsilon */                     { $$ = NULL; }
    ;
Type:
    INT PosEndL     { $$ = INT_TYPE; }
    | BOOL PosEndL  { $$ = BOOL_TYPE; }
    ;
StatementSequence:
    Statement SC PosEndL StatementSequence  { $$ = appendSmt($1, $4); } // modify $1 statement struct to have $3 as *next
    | /* epsilon */                 { $$ = NULL; }
    ;
Statement:
    Assignment PosEndL          { $$ = buildS(ASN_SMT, $1); }
    | IfStatement PosEndL       { $$ = buildS(IF_SMT, $1); }
    | WhileStatement PosEndL    { $$ = buildS(WHILE_SMT, $1); }
    | WriteInt PosEndL          { $$ = buildS(WRITE_SMT, $1); }
    ;
Assignment:
    IDENT PosEndL ASGN PosEndL Expression   { $$ = buildA(EXP_ASN, $1, $5); }
    | IDENT PosEndL ASGN PosEndL READINT PosEndL    { $$ = buildA(READ_ASN, $1, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
IfStatement:
    IF PosEndL Expression THEN PosEndL StatementSequence ElseClause END PosEndL { $$ = buildI($3, $6, $7); }
    ;
ElseClause:
    ELSE PosEndL StatementSequence  { $$ = $3; }
    | /* epsilon */         { $$ = NULL; }
    ;
WhileStatement:
    WHILE PosEndL Expression DO PosEndL StatementSequence END PosEndL   { $$ = buildW($3, $6); }
    ;
WriteInt:
    WRITEINT PosEndL Expression { $$ = $3; }
    ;
Expression:
    SimpleExpression EQUAL PosEndL SimpleExpression     { $$ = buildE($1, EQUAL_OP, $4); }
    | SimpleExpression NEQUAL PosEndL SimpleExpression  { $$ = buildE($1, NEQUAL_OP, $4); }
    | SimpleExpression LT PosEndL SimpleExpression      { $$ = buildE($1, LT_OP, $4); }
    | SimpleExpression GT PosEndL SimpleExpression      { $$ = buildE($1, GT_OP, $4); }
    | SimpleExpression LTE PosEndL SimpleExpression     { $$ = buildE($1, LTE_OP, $4); }
    | SimpleExpression GTE PosEndL SimpleExpression     { $$ = buildE($1, GTE_OP, $4); }
    | SimpleExpression                          { $$ = buildE($1, NO_EXP_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
SimpleExpression:
    Term PLUS PosEndL Term      { $$ = buildSE($1, PLUS_OP, $4); }
    | Term DASH PosEndL Term    { $$ = buildSE($1, MINUS_OP, $4); }
    | Term              { $$ = buildSE($1, NO_SEXP_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
Term:
    Factor MULT PosEndL Factor  { $$ = buildT($1, MULT_OP, $4); }
    | Factor DIV PosEndL Factor { $$ = buildT($1, DIV_OP, $4); }
    | Factor MOD PosEndL Factor { $$ = buildT($1, MOD_OP, $4); }
    | Factor            { $$ = buildT($1, NO_TERM_OP, NULL); } // pass dummy param to avoid overcomplicating with variadic
    ;
Factor:
    IDENT PosEndL               { $$ = buildF(ID_FACT, $1); }
    | NUMBER PosEndL            { $$ = buildF(NUM_FACT, $1); }
    | BOOLEAN PosEndL           { $$ = buildF(BOOL_FACT, $1); }
    | LP PosEndL Expression RP PosEndL  { $$ = buildF(SUB_EXP_FACT, $3); }
    ;
PosEndL:
    ENDL PosEndL
    | /* epsilon */
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

declaration *buildD(char *id, type type, declaration *next) {
    declaration *ptr;
	if ((ptr = malloc(sizeof(declaration))) == NULL) {
		yyerror("out of memory");
	}
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

assignment *buildA(asnType type, char* id, exp* exp) {
    assignment *ptr;
	if ((ptr = malloc(sizeof(assignment))) == NULL) {
		yyerror("out of memory");
	}
    ptr->type = type;
    ptr->id = id;
    ptr->exp = exp;
    return ptr;
}

ifState *buildI(exp *exp, statement *thenC, statement *elseC) {
    ifState *ptr;
	if ((ptr = malloc(sizeof(ifState))) == NULL) {
		yyerror("out of memory");
	}
    ptr->exp = exp;
    ptr->thenC = thenC;
    ptr->elseC = elseC;
    return ptr;
}

whileState *buildW(exp *exp, statement *doC) {
    whileState *ptr;
	if ((ptr = malloc(sizeof(whileState))) == NULL) {
		yyerror("out of memory");
	}
    ptr->exp = exp;
    ptr->doC = doC;
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
