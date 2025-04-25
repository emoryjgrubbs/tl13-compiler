typedef struct program program; 
typedef struct declaration declaration;
typedef enum { INT_TYPE, BOOL_TYPE } type;
typedef struct statement statement;
typedef struct assignment assignment;
typedef struct ifState ifState;
typedef struct whileState whileState;
typedef struct writeState writeState;
typedef struct exp exp;
typedef struct sExp sExp;
typedef struct term term;
typedef struct fact fact;
typedef enum { FALSE_BOOL, TRUE_BOOL } boolVal;

struct program {
    declaration *decls;
    statement *smts;
};

struct declaration {
    int line;
    char *id;
    type type;
    declaration *next; // linked list of declaration
};

typedef enum { ASN_SMT, IF_SMT, WHILE_SMT, WRITE_SMT } smtType;
struct statement {
    smtType type;
    union {
        assignment *asn;
        ifState *ifS;
        whileState *whileS;
        writeState *write;
    } smt;  // union of statement types
    statement *next;
};

typedef enum { EXP_ASN, READ_ASN } asnType;
struct assignment {
    int line;
    asnType type;
    char *id;
    exp *exp;
};

struct ifState {
    int line;
    exp *exp;
    statement *thenC; // pointer to list of statements in then clause
    statement *elseC; // pointer to list of statements in else clause
};

struct whileState {
    int line;
    exp *exp;
    statement *doC; // pointer to list of statements to excecute in while loop
};

struct writeState {
    int line;
    exp *exp;
};

typedef enum { EQUAL_OP, NEQUAL_OP, LT_OP, GT_OP, LTE_OP, GTE_OP, NO_EXP_OP } expOp;
struct exp {
    sExp *sExpOne;
    expOp op;
    sExp *sExpTwo;
};

typedef enum { PLUS_OP, MINUS_OP, NO_SEXP_OP } sExpOp;
struct sExp {
    term *termOne;
    sExpOp op;
    term *termTwo;
};

typedef enum { MULT_OP, DIV_OP, MOD_OP, NO_TERM_OP } termOp;
struct term {
    fact *factOne;
    termOp op;
    fact *factTwo;
};

// union type of different factor types
typedef enum { ID_FACT, NUM_FACT, BOOL_FACT, SUB_EXP_FACT } factType;
struct fact {
    factType type;
    union {
        char *id;
        int num;
        boolVal boole;
        exp *subExp;
    } value;
};

typedef struct error {
    // int line;
    int place;
    int len1;
    int skip;
    int len2;
    char *info;

    struct error *next;
} error;

typedef struct expInfo {
    type type;
    char* inStr;
    char* outStr;

    error *errors;
} expInfo;

int genProg(program *);
int genDecls(declaration *);
int genSmts(statement *, int);
int genAsn(assignment *, int);
int genIf(ifState *, int);
int genWhile(whileState *, int);
int genWrite(writeState *, int);
expInfo *genExp(exp *);
expInfo *genSExp(sExp *);
expInfo *genTerm(term *);
expInfo *genFact(fact *);
