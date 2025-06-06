#include <stdlib.h>
#include "uthash.h"
#include <stdio.h>
#include <string.h>
#include "tl13.h"

// leaving yellow in incase i do warnings, but unlikely
#define ANSI_COLOR_RED          "\x1b[31m"
#define ANSI_COLOR_LIGHT_RED    "\x1b[91m"
#define ANSI_COLOR_YELLOW       "\x1b[33m"
#define ANSI_COLOR_LIGHT_YELLOW "\x1b[93m"
#define ANSI_COLOR_RESET        "\x1b[0m"

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

boolVal errors = 0;

int writeOutput(outputLine *line) {
    if (!line) { return 0; }
    writeOutput(line->next);

    for (int i = 0; i < line->indents; i++ ) { printf("\t"); }
    // not really sure what's up but adding new lines on the outputLine
    //  strs adds a 1 after the if statement str when printing here
    printf("%s\n", line->str);

    free(line);
    return 0;
}

int freeOutput(outputLine *line) {
    if (!line) { return 0; }
    freeOutput(line->next);

    free(line);
    return 0;
}

int genProg(program *p) {
    if (!p) { return 0; }

    struct outputLine *headerLine;
    if ((headerLine = malloc(sizeof(outputLine))) == NULL) {}
    // generic includes and main function
    headerLine->str = "#include <stdio.h>\n#include <stdbool.h>\nint main(void) {";
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
    footerLine->str = "\treturn 0;\n}";
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
        writeOutput(output);
        return 0;
    }
    else {
        // free output since not freed while printing
        freeOutput(output);
        printf("\tEncountered " ANSI_COLOR_LIGHT_RED "%d" ANSI_COLOR_RESET " errors\n", errors);
    }

    //abort();
    return 1;
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
            printf("\t%-5dvar %s as %s ; <-- Duplicate delcaration of previously declared\n", p->line, p->id, declType);
            printf("\t         ");
            for (int i = 0; i < strlen(p->id); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
            printf("\n\n");
        }
        else {
            printf("\t%-5dvar %s as %s ; <-- Conflicting delcaration of previously declared\n", p->line, p->id, declType);
            printf("\t         ");
            for (int i = 0; i < strlen(p->id); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
            printf("\n\n");
        }
        errors++;

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
    if ((str = malloc(strlen(declType) + sizeof(p->id) + strlen(" ;"))) == NULL) {}
    strcpy(str, declType);
    strcat(str, " ");
    strcat(str, p->id);
    strcat(str, ";");
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
    }

    // generate next statement
    genSmts(p->next, indents);

    free(p);
    return 0;
}

int printExpErrors(int line, char *smt, int smtPlace, error *err) {
    if (!err) { return 0; }
    printExpErrors(line, smt, smtPlace, err->next);
    printf("\t%-5d%s <-- %s\n\t", line, smt, err->info);
    printf("     ");
    for (int i = 0; i < smtPlace; i++) { printf(" "); }
    for (int i = 0; i < err->place; i++ ) { printf(" "); }
    for (int i = 0; i < err->len1; i++ ) { printf(ANSI_COLOR_LIGHT_RED "^"); }
    for (int i = 0; i < err->skip; i++ ) { printf(" "); }
    for (int i = 0; i < err->len2; i++ ) { printf(ANSI_COLOR_LIGHT_RED "^"); }
    printf(ANSI_COLOR_RESET"\n\n");

    errors++;

    free(err);
    err = NULL;
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
        printf("\t%-5d%s := %s ; <-- Assigning %s to undeclared\n", p->line, p->id, exp->inStr, expTypeStr);
        printf("\t     ");
        for (int i = 0; i < strlen(p->id); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
        printf("\n\n");
        errors++;

        // print the expression's errors
        if (exp->errors) {
            char *smt;
            if ((smt = malloc(sizeof(p->id) + strlen(" := ") + strlen(exp->inStr) + strlen(" ;"))) == NULL) {}
            strcpy(smt, p->id);
            strcat(smt, " := ");
            strcat(smt, exp->inStr);
            strcat(smt, " ;");
            printExpErrors(p->line,  smt, strlen(p->id) + strlen(" := "), exp->errors);
        }

        free(exp);
        free(p);
        return 0;
    }

    if (p->type == EXP_ASN){
        expInfo *exp = genExp(p->exp);
        if ((exp->type != -1) && (ent->varType != exp->type)) {
            char *varTypeStr;
            switch (ent->varType) {
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
            printf("\t%-5d%s := %s ; <-- Assigning %s to %s\n", p->line, p->id, exp->inStr, expTypeStr, varTypeStr);
            printf("\t     ");
            for (int i = 0; i < strlen(p->id); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
            printf("    ");
            for (int i = 0; i < strlen(exp->inStr); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
            printf("\n\n");
            errors++;
        }
        else {
            struct outputLine *line;
            if ((line = malloc(sizeof(outputLine))) == NULL) {}
            char *str;
            if ((str = malloc(sizeof(p->id) + strlen(" = ") + strlen(exp->outStr) + strlen(";"))) == NULL) {}
            strcpy(str, p->id);
            strcat(str, " = ");
            strcat(str, exp->outStr);
            strcat(str, ";");
            line->str = str;
            line->indents = indents;
            line->next = output;
            output = line;

            // TODO ask about if it should auto be changed to initialized?
            ent->initialized = TRUE_BOOL;
        }

        // print the expression's errors
        if (exp->errors) {
            char *smt;
            if ((smt = malloc(sizeof(p->id) + strlen(" := ") + strlen(exp->inStr) + strlen(" ;"))) == NULL) {}
            strcpy(smt, p->id);
            strcat(smt, " := ");
            strcat(smt, exp->inStr);
            strcat(smt, " ;");
            printExpErrors(p->line, smt, strlen(p->id) + strlen(" := "), exp->errors);
        }

        free(exp);
    }
    else if (p->type == READ_ASN){
        if (ent->varType != INT_TYPE) {
            printf("\t%-5d%s := readInt ; <-- Assigning implicit read INT to BOOL\n", p->line, p->id);
            printf("\t     ");
            for (int i = 0; i < strlen(p->id); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
            printf("    " ANSI_COLOR_LIGHT_RED "^^^^^^^" ANSI_COLOR_RESET "\n\n");
            errors++;
        }
        else {
            struct outputLine *printLine;
            if ((printLine = malloc(sizeof(outputLine))) == NULL) {}
            printLine->str = "printf(\"Enter a number: \");";
            printLine->indents = indents;
            printLine->next = output;
            output = printLine;

            struct outputLine *scanLine;
            if ((scanLine = malloc(sizeof(outputLine))) == NULL) {}
            char *str;
            if ((str = malloc(strlen("scanf(\"%d\", &") + sizeof(p->id) + strlen(");"))) == NULL) {}
            strcpy(str, "scanf(\"%d\", &");
            strcat(str, p->id);
            strcat(str, ");");
            scanLine->str = str;
            scanLine->indents = indents;
            scanLine->next = output;
            output = scanLine;
        }
    }

    free(p);
    return 0;
}
int genIf(ifState *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != BOOL_TYPE)) {
        printf("\t%-5dif %s then ... end ; <-- If conditional must be of type BOOL\n", p->line, exp->inStr);
        printf("\t        ");
        for (int i = 0; i < strlen(exp->inStr); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
        printf("\n\n");
        errors++;
    }
    // print the expression's errors
    else if (exp->errors) {
        char *smt;
        if ((smt = malloc(strlen("if ") + strlen(exp->inStr) + strlen(" then ... end ;"))) == NULL) {}
        strcpy(smt, "if ");
        strcat(smt, exp->inStr);
        strcat(smt, " then ... end ;");
        printExpErrors(p->line, smt, strlen("if "), exp->errors);
    }
    else {
        struct outputLine *line;
        if ((line = malloc(sizeof(outputLine))) == NULL) {}
        char *str;
        if ((str = malloc(strlen("if (") + sizeof(exp->outStr) + strlen(")"))) == NULL) {}
        strcpy(str, "if (");
        strcat(str, exp->outStr);
        strcat(str, ") {");
        line->str = str;
        line->indents = indents;
        line->next = output;
        output = line;
    }

    free(exp); 

    genSmts(p->thenC, indents+1);

    struct outputLine *EndIfLine;
    if ((EndIfLine = malloc(sizeof(outputLine))) == NULL) {}
    EndIfLine->str = "}";
    EndIfLine->indents = indents;
    EndIfLine->next = output;
    output = EndIfLine;

    // if there is no else, don't print it
    if (!p->elseC) { free(p); return 0; }

    struct outputLine *BeginElseLine;
    if ((BeginElseLine = malloc(sizeof(outputLine))) == NULL) {}
    BeginElseLine->str = "else {";
    BeginElseLine->indents = indents;
    BeginElseLine->next = output;
    output = BeginElseLine;

    genSmts(p->elseC, indents+1);

    struct outputLine *EndElseLine;
    if ((EndElseLine = malloc(sizeof(outputLine))) == NULL) {}
    EndElseLine->str = "}";
    EndElseLine->indents = indents;
    EndElseLine->next = output;
    output = EndElseLine;

    free(p);
    return 0;
}
int genWhile(whileState *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != BOOL_TYPE)) {
        printf("\t%-5dwhile %s do ... end ; <-- While conditional must be of type BOOL\n", p->line, exp->inStr);
        printf("\t           ");
        for (int i = 0; i < strlen(exp->inStr); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
        printf("\n\n");
        errors++;
    }
    // print the expression's errors
    else if (exp->errors) {
        char *smt;
        if ((smt = malloc(strlen("while ") + strlen(exp->inStr) + strlen(" do ... end ;"))) == NULL) {}
        strcpy(smt, "while ");
        strcat(smt, exp->inStr);
        strcat(smt, " do ... end ;");
        printExpErrors(p->line, smt, strlen("while "), exp->errors);
    }
    else {
        struct outputLine *line;
        if ((line = malloc(sizeof(outputLine))) == NULL) {}
        char *str;
        if ((str = malloc(strlen("while (") + sizeof(exp->outStr) + strlen(") {"))) == NULL) {}
        strcpy(str, "while (");
        strcat(str, exp->outStr);
        strcat(str, ") {");
        line->str = str;
        line->indents = indents;
        line->next = output;
        output = line;
    }

    free(exp);

    genSmts(p->doC, indents+1);

    // build closing line
    struct outputLine *line;
    if ((line = malloc(sizeof(outputLine))) == NULL) {}
    line->str = "}";
    line->indents = indents;
    line->next = output;
    output = line;

    free(p);
    return 0;
}
int genWrite(writeState *p, int indents) {
    expInfo *exp = genExp(p->exp);

    if ((exp->type != -1) && (exp->type != INT_TYPE)) {
        printf("\t%-5dwriteInt %s ; <-- Write expression must be of type INT\n", p->line, exp->inStr);
        printf("\t              ");
        for (int i = 0; i < strlen(exp->inStr); i++) { printf(ANSI_COLOR_LIGHT_RED "^" ANSI_COLOR_RESET); }
        printf("\n\n");
        errors++;
    }

    // print the expression's errors
    if (exp->errors) {
        char *smt;
        if ((smt = malloc(strlen("writeInt ") + strlen(exp->inStr) + strlen(" ;"))) == NULL) {}
        strcpy(smt, "writeInt ");
        strcat(smt, exp->inStr);
        strcat(smt, " ;");
        printExpErrors(p->line, smt, strlen("writeInt "), exp->errors);
    }

    struct outputLine *line;
    if ((line = malloc(sizeof(outputLine))) == NULL) {}
    char *str;
    if ((str = malloc(strlen("printf(\"%d\\n\", ") + sizeof(exp->outStr) + strlen(");"))) == NULL) {}
    strcpy(str, "printf(\"%d\\n\", ");
    strcat(str, exp->outStr);
    strcat(str, ");");
    line->str = str;
    line->indents = indents;
    line->next = output;
    output = line;

    free(exp);
    return 0;
}

int errCat(error *p1, error *p2) {
    if (!p1) { p1 = p2; }
    else if (!p1->next) { p1->next = p2; }
    else { errCat(p1->next, p2); }
    return 0;
}

int errPushPlace(error *p, int leftLen) {
    if (!p) { return 0; }
    p->place += leftLen;
    errPushPlace(p->next, leftLen);
    return 0;
}

expInfo *genExp(exp* p) {
    struct expInfo *info;
    if ((info = malloc(sizeof(expInfo))) == NULL) {}
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
    int side = 0;
    struct error *err;
    if ((sInfo1->type != -1) && (sInfo1->type == BOOL_TYPE)) { side += 1; }
    if ((sInfo2->type != -1) && (sInfo2->type == BOOL_TYPE)) { side += 2; }
    switch (p->op) {
        case EQUAL_OP:
            inOp = " = ";
            outOp = " == ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left equal operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right equal operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right equal operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case NEQUAL_OP:
            inOp = " != ";
            outOp = " != ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left not-equal operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right not-equal operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right not-equal operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case LT_OP:
            inOp = " < ";
            outOp = " < ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left less-than operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right less-than operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right less-than operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case GT_OP:
            inOp = " > ";
            outOp = " > ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left greater-than operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right greater-than operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right greater-than operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case LTE_OP:
            inOp = " <= ";
            outOp = " <= ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left less-than-equal-to operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right less-than-equal-to operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right less-than-equal-to operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case GTE_OP:
            inOp = " >= ";
            outOp = " >= ";
            type = BOOL_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left greater-than-equal-to operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right greater-than-equal-to operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right greater-than-equal-to operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case NO_EXP_OP:
            inOp = "";
            outOp = "";
            type = sInfo1->type;
            info->errors = sInfo1->errors;
    }
    // build info
    info->type = type;
    if ((inStr = malloc(strlen(sInfo1->inStr) + strlen(inOp) + strlen(sInfo2->inStr))) == NULL) {}
    strcpy(inStr, sInfo1->inStr);
    strcat(inStr, inOp);
    strcat(inStr, sInfo2->inStr);
    info->inStr = inStr;
    if ((outStr = malloc(strlen(sInfo1->outStr) + strlen(outOp) + strlen(sInfo2->outStr))) == NULL) {}
    strcpy(outStr, sInfo1->outStr);
    strcat(outStr, outOp);
    strcat(outStr, sInfo2->outStr);
    info->outStr = outStr;

    free(sInfo1);
    free(sInfo2);
    free(p);
    return info;
}

expInfo *genSExp(sExp* p) {
    struct expInfo *info;
    if ((info = malloc(sizeof(expInfo))) == NULL) {}
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
    int side = 0;
    struct error *err;
    if ((sInfo1->type != -1) && (sInfo1->type == BOOL_TYPE)) { side += 1; }
    if ((sInfo2->type != -1) && (sInfo2->type == BOOL_TYPE)) { side += 2; }
    switch (p->op) {
        case PLUS_OP:
            op = " + ";
            type = INT_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(op));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left addition operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right addition operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(op);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right addition operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(op);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case MINUS_OP:
            op = " - ";
            type = INT_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(op));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left subtraction operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right subtraction operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(op);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right subtraction operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(op);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info->errors = sInfo2->errors; }
            break;
        case NO_SEXP_OP:
            op = "";
            type = sInfo1->type;
            info->errors = sInfo1->errors;
    }
    // build info
    info->type = type;
    if ((inStr = malloc(strlen(sInfo1->inStr) + strlen(op) + strlen(sInfo2->inStr))) == NULL) {}
    strcpy(inStr, sInfo1->inStr);
    strcat(inStr, op);
    strcat(inStr, sInfo2->inStr);
    info->inStr = inStr;
    if ((outStr = malloc(strlen(sInfo1->outStr) + strlen(op) + strlen(sInfo2->outStr))) == NULL) {}
    strcpy(outStr, sInfo1->outStr);
    strcat(outStr, op);
    strcat(outStr, sInfo2->outStr);
    info->outStr = outStr;

    free(sInfo1);
    free(sInfo2);
    free(p);
    return info;
}

expInfo *genTerm(term *p) {
    struct expInfo *info;
    if ((info = malloc(sizeof(expInfo))) == NULL) {}
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
    struct expInfo *sInfo1 = genFact(p->factOne);
    struct expInfo *sInfo2 = genFact(p->factTwo);
    int side = 0;
    struct error *err;
    if ((sInfo1->type != -1) && (sInfo1->type == BOOL_TYPE)) { side += 1; }
    if ((sInfo2->type != -1) && (sInfo2->type == BOOL_TYPE)) { side += 2; }
    switch (p->op) {
        case MULT_OP:
            inOp = " * ";
            inOp = " * ";
            type = INT_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left multiplication operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right multiplication operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right multiplication operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case DIV_OP:
            inOp = " div ";
            inOp = " / ";
            type = INT_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left division operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right division operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right division operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case MOD_OP:
            inOp = " mod ";
            inOp = " % ";
            type = INT_TYPE;
            errPushPlace(sInfo2->errors, strlen(sInfo1->inStr) + strlen(inOp));
            // 2 before 1 to print errors in order seen (printed recursively, bottom up)
            errCat(sInfo2->errors, sInfo1->errors);
            if (side > 0) {
                if ((err = malloc(sizeof(error))) == NULL) {}
                switch (side) {
                    case 1:
                        err->info = "Left modlulo operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 2:
                        err->info = "Right modlulo operand must be of type INT";
                        err->place = strlen(sInfo1->inStr) + strlen(inOp);
                        err->len1 = strlen(sInfo2->inStr);
                        err->skip = 0;
                        err->len2 = 0;
                        break;
                    case 3:
                        err->info = "Left & Right modlulo operand must be of type INT";
                        err->place = 0;
                        err->len1 = strlen(sInfo1->inStr);
                        err->skip = strlen(inOp);
                        err->len2 = strlen(sInfo2->inStr);
                }
                err->next = sInfo2->errors;
                info->errors = err;
            }
            else { info-> errors = sInfo2->errors; }
            break;
        case NO_TERM_OP:
            inOp = "";
            outOp = "";
            type = sInfo1->type;
            info-> errors = sInfo1->errors;
    }
    // build info
    info->type = type;
    if ((inStr = malloc(strlen(sInfo1->inStr) + strlen(inOp) + strlen(sInfo2->inStr))) == NULL) {}
    strcpy(inStr, sInfo1->inStr);
    strcat(inStr, inOp);
    strcat(inStr, sInfo2->inStr);
    info->inStr = inStr;
    if ((outStr = malloc(strlen(sInfo1->outStr) + strlen(outOp) + strlen(sInfo2->outStr))) == NULL) {}
    strcpy(outStr, sInfo1->outStr);
    strcat(outStr, outOp);
    strcat(outStr, sInfo2->outStr);
    info->outStr = outStr;

    free(sInfo1);
    free(sInfo2);
    free(p);
    return info;
}

expInfo *genFact(fact *p) {
    struct expInfo *info;
    if (!p) {
        if ((info = malloc(sizeof(expInfo))) == NULL) {}
        info->type = -1;
        info->inStr = "";
        info->outStr = "";
        info->errors = NULL;
        return info;
    }
    switch (p->type) {
        case ID_FACT:
            if ((info = malloc(sizeof(expInfo))) == NULL) {}
            struct tblEntry *ent;
            HASH_FIND_STR(entries, p->value.id, ent);
            if (ent != NULL) {
                info->type = ent->varType;
                info->inStr = p->value.id;
                info->outStr = p->value.id;
                info->errors = NULL;
                if (ent->initialized == FALSE_BOOL) {
                    // comply with informal semantics (uninitialized ints considered 0, bools false)
                    info->outStr = "0";
                    /* TODO make warning? or just delete
                    struct error *err;
                    if ((err = malloc(sizeof(error))) == NULL) {}
                    err->info = "Use of uninitialized";
                    err->next = NULL;
                    info->errors = err;
                    */
                }
            }
            else {
                info->type = -1;
                info->inStr = p->value.id;
                info->outStr = p->value.id;
                struct error *err;
                if ((err = malloc(sizeof(error))) == NULL) {}
                char *str;
                char *message = "Use of undeclared: ";
                if ((str = malloc(strlen(message) + sizeof(p->value.id))) == NULL) {}
                strcpy(str, message);
                strcat(str, p->value.id);
                err->info = str;
                err->place = 0;
                err->len1 = strlen(info->inStr);
                err->skip = 0;
                err->len2 = 0;
                err->next = NULL;
                info->errors = err;
            }
            break;
        case NUM_FACT:
            if ((info = malloc(sizeof(expInfo))) == NULL) {}
            info->type = INT_TYPE;
            int size;
            if (p->value.num > 0) { size = 0; }
            else { size = 1; }
            int remaining = p->value.num;
            // choose between a few more instructions or a few more bytes of storage per
            while (remaining) {
                remaining /= 10;
                size += 1;
            }
            if ((info->inStr = malloc(size)) == NULL) {}
            if ((info->outStr = malloc(size)) == NULL) {}
            sprintf(info->inStr, "%d", p->value.num);
            sprintf(info->outStr, "%d", p->value.num);
            info->errors = NULL;
            break;
        case BOOL_FACT:
            if ((info = malloc(sizeof(expInfo))) == NULL) {}
            info->type = BOOL_TYPE;
            if (p->value.boole == TRUE_BOOL) {
                info->inStr = "true";
                info->outStr = "true";
            }
            else if (p->value.boole == FALSE_BOOL) {
                info->inStr = "true";
                info->outStr = "true";
            }
            else { /* error */ }
            info->errors = NULL;
            break;
        case SUB_EXP_FACT:
            info = genExp(p->value.subExp);
            char *newInStr;
            if ((newInStr = malloc(strlen("()") + sizeof(info->inStr))) == NULL) {}
            strcpy(newInStr, "(");
            strcat(newInStr, info->inStr);
            strcat(newInStr, ")");
            char *newOutStr;
            if ((info->inStr = malloc(strlen(newInStr))) == NULL) {}
            info->inStr = newInStr;
            if ((newOutStr = malloc(strlen("()") + sizeof(info->outStr))) == NULL) {}
            strcpy(newOutStr, "(");
            strcat(newOutStr, info->outStr);
            strcat(newOutStr, ")");
            if ((info->outStr = malloc(strlen(newInStr))) == NULL) {}
            info->outStr = newOutStr;

            errPushPlace(info->errors, 1);
    }
    free(p);
    return info;
}
