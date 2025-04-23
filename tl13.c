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

typedef struct outputLine {
    int indents;
    char *str;

    struct outputLine *next;
} outputLine;

outputLine *output = NULL;

boolVal errors = FALSE_BOOL;

int genProg(program *p) {
    if (!p) { return 0; }

    struct outputLine *headerLine;
    if ((headerLine = malloc(sizeof(outputLine))) == NULL) {}
    // generic includes and main function
    headerLine->str = "#include <stdio.h>\n#include <stdbool.h>\nint main(void) {\n";
    headerLine->indents = 0;
    // shouldn't be nessesary
    headerLine->next = output;
    output = headerLine;

    // print delcarations
    genDecls(p->decls);

    // print statements
    genSmts(p->smts, 1);

    struct outputLine *footerLine;
    if ((footerLine = malloc(sizeof(outputLine))) == NULL) {}
    // generic includes and main function
    footerLine->str = "\treturn 0;\n}\n";
    footerLine->indents = 0;
    footerLine->next = output;
    output = footerLine;

    // clear all hash table entries
    struct tblEntry *ent;
    struct tblEntry *tmp;

    HASH_ITER(hh, entries, ent, tmp) {
        HASH_DEL(entries, ent);
        free(ent);
    }

    // free final node pointer
    free(p);

    // if there are no errors, print the output code
    if (!errors) {
        //print output
    }

    return 0;
}

int genDecls(declaration *p) {
    if (!p) { return 0; }

    struct tblEntry *ent;
    HASH_FIND_STR(entries, p->id, ent);

    // get declaration type
    char *declType;
    if (p->type == INT_TYPE) { declType = "int"; }
    else { declType = "bool"; }

    // declaration already exists, (INFORMAL TYPE RULES ENFORCEMENT)
    if (ent != NULL) {
        if (p->type == ent->varType) {
            printf("var %s as %s ;\t<--\tDuplicate delcaration of previously declared", p->id, declType);
        }
        else {
            printf("var %s as %s ;\t<--\tConflicting delcaration of previously declared", p->id, declType);
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

    struct outputLine *line;
    if ((line = malloc(sizeof(outputLine))) == NULL) {}
    char *str;
    if ((str = malloc(strlen(declType) + sizeof(p->id) + strlen(";\n"))) == NULL) {}
    strcpy(str, declType);
    strcat(str, p->id);
    strcat(str, ";\n");
    line->str = str;
    line->indents = 1;
    line->next = output;
    output = line;

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
        expInfo *exp = genExp(p->exp);
        char *expTypeStr;
        switch (exp->type) {
            case INT_TYPE:
                expTypeStr = "INT";
                break;
            case BOOL_TYPE:
                expTypeStr = "BOOL";
                break;
            default:
                expTypeStr = "UNKNOWN";
        }
        printf("%s := %s ;\t<--\tAssigning %s to undeclared\n", p->id, exp->inStr, expTypeStr);

        // TODO read list of errors from exp and print and free

        free(p);
        return 0;
    }



    if (p->type == EXP_ASN){
        expInfo *exp = genExp(p->exp);
        if ((exp->type != -1) && (ent->varType != exp->type)) {
            char *varTypeStr;
            switch (exp->type) {
                case INT_TYPE:
                    varTypeStr = "INT";
                    break;
                case BOOL_TYPE:
                    varTypeStr = "BOOL";
                    break;
                default:
                    varTypeStr = "UNKNOWN";
            }
            char *expTypeStr;
            switch (exp->type) {
                case INT_TYPE:
                    expTypeStr = "INT";
                    break;
                case BOOL_TYPE:
                    expTypeStr = "BOOL";
                    break;
                default:
                    expTypeStr = "UNKNOWN";
            }
            printf("%s := %s ;\t<--\tAssigning %s to %s\n", p->id, exp->inStr, expTypeStr, varTypeStr);
        }
        else {
            struct outputLine *line;
            if ((line = malloc(sizeof(outputLine))) == NULL) {}
            char *str;
            if ((str = malloc(sizeof(p->id) + strlen(" = ") + strlen(exp->outStr) + strlen(";\n"))) == NULL) {}
            strcpy(str, p->id);
            strcat(str, " = ");
            strcat(str, exp->outStr);
            strcat(str, ";\n");
            line->str = str;
            line->indents = indents;
            line->next = output;
            output = line;

            // TODO ask about if it should auto be changed to initialized?
            ent->initialized = TRUE_BOOL;
        }
    }
    else if (p->type == READ_ASN){
        if (ent->varType != INT_TYPE) {
            printf("%s := readInt ;\t<--\tAssigning implicit read INT to BOOL\n", p->id);
        }
        else {
            struct outputLine *printLine;
            if ((printLine = malloc(sizeof(outputLine))) == NULL) {}
            printLine->str = "printf(\"Enter a number: \");\n";
            printLine->indents = indents;
            printLine->next = output;
            output = printLine;

            struct outputLine *scanLine;
            if ((scanLine = malloc(sizeof(outputLine))) == NULL) {}
            char *str;
            if ((str = malloc(sizeof(p->id) + strlen(" = scanf(\"%%d\", &") + sizeof(p->id) + strlen(");\n"))) == NULL) {}
            strcpy(str, p->id);
            strcat(str, " = scanf(\"%%d\", &");
            strcat(str, p->id);
            strcat(str, ");\n");
            scanLine->str = str;
            scanLine->indents = indents;
            scanLine->next = output;
            output = scanLine;
        }
    }

    // TODO read list of errors from exp and print and free

    free(p);
    return 0;
}
int genIf(ifState *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != BOOL_TYPE)) {
        printf("if %s then ... end ;\t<--\tIf conditional must be of type BOOL", exp->inStr);
    }
    else {
        struct outputLine *line;
        if ((line = malloc(sizeof(outputLine))) == NULL) {}
        char *str;
        if ((str = malloc(strlen("if (") + sizeof(exp->outStr) + strlen(") {\n"))) == NULL) {}
        strcpy(str, "if (");
        strcat(str, exp->outStr);
        strcat(str, ") {\n");
        line->str = str;
        line->indents = indents;
        line->next = output;
        output = line;
    }

    // TODO read list of errors from exp and print and free

    genSmts(p->thenC, indents+1);

    struct outputLine *EndIfLine;
    if ((EndIfLine = malloc(sizeof(outputLine))) == NULL) {}
    EndIfLine->str = "}\n";
    EndIfLine->indents = indents;
    EndIfLine->next = output;
    output = EndIfLine;

    // if there is no else, don't print it
    if (!p->elseC) { free(p); return 0; }

    struct outputLine *BeginElseLine;
    if ((BeginElseLine = malloc(sizeof(outputLine))) == NULL) {}
    BeginElseLine->str = "else {\n";
    BeginElseLine->indents = indents;
    BeginElseLine->next = output;
    output = BeginElseLine;

    genSmts(p->elseC, indents+1);

    struct outputLine *EndElseLine;
    if ((EndElseLine = malloc(sizeof(outputLine))) == NULL) {}
    EndElseLine->str = "}\n";
    EndElseLine->indents = indents;
    EndElseLine->next = output;
    output = EndElseLine;

    free(p);
    return 0;
}
int genWhile(whileState *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != BOOL_TYPE)) {
        printf("if %s then ... end ;\t<--\tWhile conditional must be of type BOOL", exp->inStr);
    }
    else {
        struct outputLine *line;
        if ((line = malloc(sizeof(outputLine))) == NULL) {}
        char *str;
        if ((str = malloc(strlen("while (") + sizeof(exp->outStr) + strlen(") {\n"))) == NULL) {}
        strcpy(str, "while (");
        strcat(str, exp->outStr);
        strcat(str, ") {\n");
        line->str = str;
        line->indents = indents;
        line->next = output;
        output = line;
    }

    // TODO read list of errors from exp and print and free

    genSmts(p->doC, indents+1);

    // build closing line
    struct outputLine *line;
    if ((line = malloc(sizeof(outputLine))) == NULL) {}
    line->str = "}\n";
    line->indents = indents;
    line->next = output;
    output = line;

    free(p);
    return 0;
}
int genWrite(exp *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != BOOL_TYPE)) {
        printf("writeInt %s ;\t<--\tWrite expression must be of type INT", exp->inStr);
    }

    // TODO read list of errors from exp and print and free

    struct outputLine *line;
    if ((line = malloc(sizeof(outputLine))) == NULL) {}
    char *str;
    if ((str = malloc(strlen("printf(\"%%d\\n\", ") + sizeof(exp->outStr) + strlen(");\n"))) == NULL) {}
    strcpy(str, "printf(\"%%d\\n\", ");
    strcat(str, exp->outStr);
    strcat(str, ");\n");
    line->str = str;
    line->indents = indents;
    line->next = output;
    output = line;

    return 0;
}

int errCat(error *p1, error *p2) {
    if (!p1) { p1 = p2; }
    else if (!p1->next) { p1->next = p2; }
    else { errCat(p1->next, p2); }
    return 0;
}

expInfo *genExp(exp* p) {
    struct expInfo *info;
    if (!p) {
        info->type = -1;
        info->inStr = "";
        info->outStr = "";
        info->errors = NULL;
        return info;
    }
    char *inStr;
    char *outStr;
    char *inOp;
    char *outOp;
    int type;
    struct expInfo *sInfo1 = genSExp(p->sExpOne);
    struct expInfo *sInfo2 = genSExp(p->sExpTwo);
    // 2 before 1 to print errors in order seen (printed recursively, bottom up)
    errCat(sInfo2->errors, sInfo1->errors);
    int side = 0;
    struct error *err;
    if ((sInfo1->type != -1) && (sInfo1->type == BOOL_TYPE)) { side += 1; }
    if ((sInfo2->type != -1) && (sInfo2->type == BOOL_TYPE)) { side += 2; }
    switch (p->op) {
        case EQUAL_OP:
            inOp = " = ";
            outOp = " == ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left equal operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right equal operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right equal operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case NEQUAL_OP:
            inOp = " != ";
            outOp = " != ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left not-equal operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right not-equal operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right not-equal operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case LT_OP:
            inOp = " < ";
            outOp = " < ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left less-than operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right less-than operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right less-than operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case GT_OP:
            inOp = " > ";
            outOp = " > ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left greater-than operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right greater-than operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right greater-than operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case LTE_OP:
            inOp = " <= ";
            outOp = " <= ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left less-than-equal-to operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right less-than-equal-to operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right less-than-equal-to operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case GTE_OP:
            inOp = " >= ";
            outOp = " >= ";
            type = BOOL_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left greater-than-equal-to operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right greater-than-equal-to operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right greater-than-equal-to operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case NO_EXP_OP:
            inOp = "";
            outOp = "";
            type = sInfo1->type;
            info-> errors = sInfo1->errors;
            break;
    }
    // build info
    info->type = type;
    if ((inStr = malloc(strlen(sInfo1->inStr) + strlen(inOp) + strlen(sInfo2->inStr))) == NULL) {}
    strcpy(inStr, sInfo1->inStr);
    strcat(inStr, inOp);
    strcat(inStr, sInfo2->inStr);
    info->inStr = inStr;
    if ((outStr = malloc(strlen(sInfo1->outStr) + strlen(outOp) + strlen(sInfo2->outStr))) == NULL) {}
    strcpy(inStr, sInfo1->outStr);
    strcat(inStr, outOp);
    strcat(inStr, sInfo2->outStr);
    info->outStr = outStr;

    free(p);
    return info;
}

expInfo *genSExp(sExp* p) {
    struct expInfo *info;
    if (!p) {
        info->type = -1;
        info->inStr = "";
        info->outStr = "";
        info->errors = NULL;
        return info;
    }
    char *inStr;
    char *outStr;
    char *op;
    int type;
    struct expInfo *sInfo1 = genTerm(p->termOne);
    struct expInfo *sInfo2 = genTerm(p->termTwo);
    // 2 before 1 to print errors in order seen (printed recursively, bottom up)
    errCat(sInfo2->errors, sInfo1->errors);
    int side = 0;
    struct error *err;
    if ((sInfo1->type != -1) && (sInfo1->type == BOOL_TYPE)) { side += 1; }
    if ((sInfo2->type != -1) && (sInfo2->type == BOOL_TYPE)) { side += 2; }
    switch (p->op) {
        case PLUS_OP:
            op = " + ";
            type = INT_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left addition operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right addition operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right addition operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case MINUS_OP:
            op = " - ";
            type = INT_TYPE;
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left subtraction operand must be of type INT";
                        break;
                    case 2:
                        err->info = "Right subtraction operand must be of type INT";
                        break;
                    case 3:
                        err->info = "Left & Right subtraction operand must be of type INT";
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case NO_SEXP_OP:
            op = "";
            type = sInfo1->type;
            info-> errors = sInfo1->errors;
    }
    // build info
    info->type = type;
    if ((inStr = malloc(strlen(sInfo1->inStr) + strlen(op) + strlen(sInfo2->inStr))) == NULL) {}
    strcpy(inStr, sInfo1->inStr);
    strcat(inStr, op);
    strcat(inStr, sInfo2->inStr);
    info->inStr = inStr;
    if ((outStr = malloc(strlen(sInfo1->outStr) + strlen(op) + strlen(sInfo2->outStr))) == NULL) {}
    strcpy(inStr, sInfo1->outStr);
    strcat(inStr, op);
    strcat(inStr, sInfo2->outStr);
    info->outStr = outStr;

    free(p);
    return info;
}

expInfo *genTerm(term *p) {
    struct expInfo *info;
    if (!p) {
        info->type = -1;
        info->inStr = "";
        info->outStr = "";
        info->errors = NULL;
        return info;
    }
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
            type = INT_TYPE;
            break;
        case DIV_OP:
        case MOD_OP:
        case NO_TERM_OP:
    }
    free(p);
    return info;
}

expInfo *genFact(fact *p) {
    struct expInfo *info;
    if (!p) {
        info->type = -1;
        info->inStr = "";
        info->outStr = "";
        info->errors = NULL;
        return info;
    }
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
    }
    free(p);
    return info;
}
