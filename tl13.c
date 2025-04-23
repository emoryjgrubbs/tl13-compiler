#include <stdlib.h>
#include "uthash.h"
#include <stdio.h>
#include <string.h>
#include "tl13.h"

typedef struct tblEntry {
    char *id;

    /* var attributes */
    boolVal initialized;
    type varType;

    UT_hash_handle hh; /* for the ut hash table */
} tblEntry;

struct tblEntry *entries = NULL;

typedef struct error {
    // int line;
    char *info;

    struct error *next;
} error;

// int line = 0;
error *errors = NULL;

int reportErr(error *err) {
    if (!err) { return 0; }

    // report all errors in errors list
    reportErr(err->next);

    printf("%s\n", err->info);

    free(err);

    return 0;
}

int genProg(program *p) {
    if (!p) { return 0; }

    // print needed inports
    printf("#include <stdio.h>\n");
    printf("#include <stdbool.h>\n");

    // print generic main
    printf("int main(void) {\n");

    // print delcarations
    genDecls(p->decls);

    // print statements
    genSmts(p->smts, 1);

    printf("\treturn 0;\n}\n");

    // clear all hash table entries
    struct tblEntry *ent;
    struct tblEntry *tmp;

    HASH_ITER(hh, entries, ent, tmp) {
        HASH_DEL(entries, ent);
        free(ent);
    }

    // free final node pointer
    free(p);

    // if there are errors, report them and abort
    if (errors) {
        printf("\n\n--- ERRORS ---\n");
        reportErr(errors);
        printf("--------------\n");
        // abort();
    }

    // execution has successfully terminated
    return 0;
}

int genDecls(declaration *p) {
    if (!p) { return 0; }

    struct tblEntry *ent;
    HASH_FIND_STR(entries, p->id, ent);

    // declaration already exists, (INFORMAL TYPE RULES ENFORCEMENT)
    if (ent != NULL) {
        struct error *err;
        if ((err = malloc(sizeof(error))) == NULL) {}
        if (p->type == ent->varType) {
            char *message = "Duplicate delcaration of previously declared: ";
            char *info;
            if ((info = malloc(strlen(message) + sizeof(p->id))) == NULL) {}
            strcpy(info, message);
            strcat(info, p->id);
            err->info = info;
            err->next = errors;
            errors = err;
        }
        else {
            char *message = "Conflicting delcaration of previously declared: ";
            char *info;
            if ((info = malloc(strlen(message) + sizeof(p->id))) == NULL) {}
            strcpy(info, message);
            strcat(info, p->id);
            err->info = info;
            err->next = errors;
            errors = err;
        }

        // generate next delcaration statement
        genDecls(p->next);

        free(p);
        return 0;
    }

    // the delcaration doesn't exist, so add it
    if ((ent = malloc(sizeof(tblEntry))) == NULL) {}
    ent->id = p->id;
    ent->initialized = FALSE_BOOL;
    ent->varType = p->type;

    HASH_ADD_STR(entries, id, ent);

    // print initial tab
    printf("\t");

    // print type
    switch (p->type) {
        case INT_TYPE:
            printf("int ");
            break;
        case BOOL_TYPE:
            printf("bool ");
            break;
        default:
            printf("");
            /* ERROR */
    }

    printf("%s;\n", p->id);

    // generate next delcaration statement
    genDecls(p->next);

    free(p);
    return 0;
}

int genSmts(statement *p, int indents) {
    if (!p) { return 0; }

    switch (p->type) {
        case ASN_SMT:
            genAsn(p->smt.asn, indents);
            break;
        case IF_SMT:
            genIf(p->smt.ifS, indents);
            break;
        case WHILE_SMT:
            genWhile(p->smt.whileS, indents);
            break;
        case WRITE_SMT:
            genWrite(p->smt.write, indents);
            break;
        default:
            printf("");
            /* ERROR */
    }

    // generate next statement
    genSmts(p->next, indents);

    free(p);
    return 0;
}

int genAsn(assignment *p, int indents) {
    struct tblEntry *ent;
    HASH_FIND_STR(entries, p->id, ent);

    // declaration for var does not exist (INFORMAL SEMANTICS ENFORCEMENT)
    if (ent == NULL) {
        struct error *err;
        if ((err = malloc(sizeof(error))) == NULL) {}
        char *message = "Assigning to undeclared: ";
        char *info;
        if ((info = malloc(strlen(message) + sizeof(p->id))) == NULL) {}
        strcpy(info, message);
        strcat(info, p->id);
        err->info = info;
        err->next = errors;
        errors = err;

        free(p);
        return 0;
    }

    // TODO ask about if it should auto be changed to initialized?
    ent->initialized = TRUE_BOOL;

    for (int i = 0; i < indents; i++) {
        printf("\t");
    }

    if (p->type == EXP_ASN){
        printf("%s = ", p->id);

        int expType = genExp(p->exp);

        if ((expType != -1) && (ent->varType != expType)) {
            char *messageP1 = "Assigning ";
            char *messageP2 = " to ";
            char *messageP3 = ": ";
            char *varTypeStr;
            if (ent->varType == INT_TYPE) { varTypeStr = "INT"; }
            else { varTypeStr = "BOOL"; }
            char *expTypeStr;
            if (expType == INT_TYPE) { expTypeStr = "INT"; }
            else { expTypeStr = "BOOL"; }
            struct error *err;
            if ((err = malloc(sizeof(error))) == NULL) {}
            char *info;
            if ((info = malloc(strlen(messageP1) + strlen(messageP2) + strlen(messageP3) + strlen(varTypeStr) + strlen(expTypeStr) + sizeof(p->id))) == NULL) {}
            strcpy(info, messageP1);
            strcat(info, expTypeStr);
            strcat(info, messageP2);
            strcat(info, varTypeStr);
            strcat(info, messageP3);
            strcat(info, p->id);
            err->info = info;
            err->next = errors;
            errors = err;
        }
    }
    else if (p->type == READ_ASN){
        if (ent->varType != INT_TYPE) {
            struct error *err;
            if ((err = malloc(sizeof(error))) == NULL) {}
            char *message = "Assigning implicit read INT to Bool: ";
            char *info;
            if ((info = malloc(strlen(message) + sizeof(p->id))) == NULL) {}
            strcpy(info, message);
            strcat(info, p->id);
            err->info = info;
            err->next = errors;
            errors = err;
        }
        printf("printf(\"Enter a number: \");\n");

        for (int i = 0; i < indents; i++) {
            printf("\t");
        }

        printf("%s = ", p->id);
        printf("scanf(\"%%d\", &%s)", p->id);
    }

    printf(";\n");
    free(p);
    return 0;
}
int genIf(ifState *p, int indents) {
    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("if (");

    int expType = genExp(p->exp);

    if ((expType != -1) && (expType != BOOL_TYPE)) {
        struct error *err;
        if ((err = malloc(sizeof(error))) == NULL) {}
        err->info = "If conditional must be of type BOOL";
        err->next = errors;
        errors = err;
    }

    printf(") {\n");

    genSmts(p->thenC, indents+1);

    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("}\n");

    // if there is no else, don't print it
    if (!p->elseC) { free(p); return 0; }

    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("else {\n");

    genSmts(p->elseC, indents+1);

    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("}\n");

    free(p);
    return 0;
}
int genWhile(whileState *p, int indents) {
    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("while (");

    int expType = genExp(p->exp);

    if ((expType != -1) && (expType != BOOL_TYPE)) {
        struct error *err;
        if ((err = malloc(sizeof(error))) == NULL) {}
        err->info = "While conditional must be of type BOOL";
        err->next = errors;
        errors = err;
    }

    printf(") {\n");

    genSmts(p->doC, indents+1);

    for (int i = 0; i < indents; i++) {
        printf("\t");
    }
    printf("}\n");

    free(p);
    return 0;
}
int genWrite(exp *p, int indents) {
    for (int i = 0; i < indents; i++) {
        printf("\t");
    }

    printf("printf(\"%%d\\n\", ");

    int expType = genExp(p);

    if ((expType != -1) && (expType != INT_TYPE)) {
        struct error *err;
        if ((err = malloc(sizeof(error))) == NULL) {}
        err->info = "Write expression must be of type INT";
        err->next = errors;
        errors = err;
    }

    printf(");\n");

    return 0;
}

int genExp(exp* p) {
    if (!p) { return 0; }
    int type;
    int sExpType;
    switch (p->op) {
        case EQUAL_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left equal operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" == ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right equal operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case NEQUAL_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left not-equal operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" != ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right not-equal operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case LT_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left less-than operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" < ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right less-than operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case GT_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left greater-than operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" > ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right greater-than operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case LTE_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left less-than-equal-to operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" <= ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right less-than-equal-to operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case GTE_OP:
            sExpType = genSExp(p->sExpOne);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left greater-than-equal-to operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" >= ");
            sExpType = genSExp(p->sExpTwo);
            if ((sExpType != -1) && (sExpType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right greater-than-equal-to operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = BOOL_TYPE;
            break;
        case NO_EXP_OP:
            sExpType = genSExp(p->sExpOne);
            type = sExpType;
            break;
        default:
            printf("");
            type = -1;
            /* ERROR */
    }
    free(p);
    return type;
}

int genSExp(sExp* p) {
    if (!p) { return 0; }
    int type;
    int termType;
    switch (p->op) {
        case PLUS_OP:
            termType = genTerm(p->termOne);
            if ((termType != -1) && (termType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left addition operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" + ");
            termType = genTerm(p->termTwo);
            if ((termType != -1) && (termType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right addition operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = INT_TYPE;
            break;
        case MINUS_OP:
            termType = genTerm(p->termOne);
            if ((termType != -1) && (termType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left subtraction operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" - ");
            termType = genTerm(p->termTwo);
            if ((termType != -1) && (termType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right subtraction operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = INT_TYPE;
            break;
        case NO_SEXP_OP:
            termType = genTerm(p->termOne);
            type = termType;
            break;
        default:
            printf("");
            type = -1;
            /* ERROR */
    }
    free(p);
    return type;
}

int genTerm(term *p) {
    if (!p) { return 0; }
    int type;
    int factType;
    switch (p->op) {
        case MULT_OP:
            factType = genFact(p->factOne);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left multiplication operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" * ");
            factType = genFact(p->factTwo);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right multiplication operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = INT_TYPE;
            break;
        case DIV_OP:
            factType = genFact(p->factOne);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left division operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" / ");
            factType = genFact(p->factTwo);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right division operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = INT_TYPE;
            break;
        case MOD_OP:
            factType = genFact(p->factOne);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Left modulo operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            printf(" %% ");
            factType = genFact(p->factTwo);
            if ((factType != -1) && (factType == BOOL_TYPE)) {
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                err->info = "Right modulo operand must be of type INT";
                err->next = errors;
                errors = err;
            }
            type = INT_TYPE;
            break;
        case NO_TERM_OP:
            factType = genFact(p->factOne);
            type = factType;
            break;
        default:
            printf("");
            type = -1;
            /* ERROR */
    }
    free(p);
    return type;
}

int genFact(fact *p) {
    if (!p) { return 0; }
    int type;
    switch (p->type) {
        case ID_FACT:
            printf("%s",p->value.id);
            struct tblEntry *ent;
            HASH_FIND_STR(entries, p->value.id, ent);
            if (ent != NULL) {
                type = ent->varType;
                if (ent->initialized == FALSE_BOOL) {
                    struct error *err;
                    if ((err = malloc(sizeof(error))) == NULL) {}
                    char *message = "Use of uninitialized: ";
                    char *info;
                    if ((info = malloc(strlen(message) + sizeof(p->value.id))) == NULL) {}
                    strcpy(info, message);
                    strcat(info, p->value.id);
                    err->info = info;
                    err->next = errors;
                    errors = err;
                }
            }
            else {
                type = -1;
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                char *message = "Use of undeclared: ";
                char *info;
                if ((info = malloc(strlen(message) + sizeof(p->value.id))) == NULL) {}
                strcpy(info, message);
                strcat(info, p->value.id);
                err->info = info;
                err->next = errors;
                errors = err;
            }
            break;
        case NUM_FACT:
            printf("%d",p->value.num);
            type = INT_TYPE;
            break;
        case BOOL_FACT:
            if (p->value.boole == TRUE_BOOL) { printf("true"); }
            else if (p->value.boole == FALSE_BOOL) { printf("false"); }
            else { /* error */ }
            type = BOOL_TYPE;
            break;
        case SUB_EXP_FACT:
            printf("(");
            type = genExp(p->value.subExp);
            printf(")");
            break;
        default:
            printf("");
            type = -1;
            /* ERROR */
    }
    free(p);
    return type;
}
