#define WINVER 0x0A00        // Alvo: Windows 10
#define _WIN32_WINNT 0x0A00  // Garante compatibilidade base do Win 10
#include <assert.h>
#include <ctype.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <windows.h>

jmp_buf env;

typedef union {
    const char *name;
    int id;
    struct {
        int param;
        int type;
        int body;
    };
    struct {
        int func;
        int arg;
    };
    struct {
        int name;
        int type;
        int value;
        int body;
    } let;
} Term;

typedef enum {
    UNIVERSE = 1,
    NAME = 2,
    ID = 4,
    LAM = 16,
    PI = 32,
    LET = 256,
    APP = 512,
    AXIOM = 1024,
    CHECK = 2048,
} Tag;

#define MAX_TERMS (2 * 1024 * 1024)
static Term *terms;
static int *term_types;
static Tag *tags;
static int *locations;
static const char **symbols;

int isfree(int name, int id);

static int terms_count = 1;
void print_term(int id) {
    Term term = terms[id];
    int paren_func, paren_arg;

    switch (tags[id]) {
    case UNIVERSE:
        printf("Type");
        return;

    case NAME:
        printf("%s", term.name);
        return;

    case ID:
        printf("%s", symbols[id]);
        return;

    case PI:
        if (isfree(term.param, term.body)) {
            paren_func = tags[term.type] & (LAM | PI);
            if (paren_func) printf("(");
            print_term(term.type);
            if (paren_func) printf(")");
            printf(" -> ");
            print_term(term.body);
        } else {
            printf("(%s : ", symbols[id]);
            print_term(term.type);
            printf(") -> ");
            print_term(term.body);
        }
        return;

    case LAM:
        printf("\\%s : ", symbols[id]);
        print_term(term.type);
        printf(". ");
        print_term(term.body);
        return;
   
    case APP:
        paren_func = tags[term.func] & (LAM | PI);
        paren_arg = tags[term.arg] & (LAM | PI | APP);

        if (paren_func) printf("(");
        print_term(term.func);
        if (paren_func) printf(")");

        printf(" ");

        if (paren_arg) printf("(");
        print_term(term.arg);
        if (paren_arg) printf(")");
        return;
    }

    printf("TAG: %d\n", tags[id]);
    longjmp(env, 1);
}

int alloc(int prev, int tag, Term term) {
    int n = terms_count++;
    tags[n] = tag;
    terms[n] = term;

    if (prev > 0) {
        symbols[n] = symbols[prev];
        locations[n] = locations[prev];
    }

    return n;
}

int isfree(int name, int id) {
    switch (tags[id]) {
    case ID:
        return name != terms[id].id;

    case PI:
    case LAM:
        if (name == terms[id].param) return 1;
        return isfree(name, terms[id].body);

    case APP:
        return isfree(name, terms[id].func) && isfree(name, terms[id].arg);

    case NAME:
        return 1;
    }
}

typedef struct {
    int names[32*1024];
    int values[32*1024];
    int count;
} Ctx;

static Ctx ctx;
static Ctx type_ctx;
static Ctx global_bindings;

void push(Ctx *ctx, int name, int value) {
    ctx->names[ctx->count] = name;
    ctx->values[ctx->count++] = value;
}

int find(Ctx *ctx, int name) {
    for (int i=ctx->count-1; i >= 0; --i) {
        if (name == ctx->names[i]) {
            return ctx->values[i];
        }
    }

    return 0;
}

int subst_id(int name, int var, int id);
static int unique = 0;

int unique_id(int base) {
    Term p;
    p.id = unique++;
    int p2 = alloc(base, ID, p);
    return p2;
}

int evaluate(int id) {
    Term t = terms[id];

    switch (tags[id]) {
    case APP:
        t.arg = evaluate(t.arg);
        t.func = evaluate(t.func);

        Term f = terms[t.func];

        if (tags[t.func] == LAM) {
            push(&ctx, f.param, t.arg);
            f.body = evaluate(f.body);
            ctx.count--;

            return f.body;
        }
 
        return alloc(id, tags[id], t);

    case PI:
    case LAM:
        t.type = evaluate(t.type);

        int new_param = unique_id(id);
        t.body = subst_id(t.param, new_param, t.body);
        t.param = terms[new_param].id;

        push(&ctx, t.param, 0);
        t.body = evaluate(t.body);
        --ctx.count;

        return alloc(id, tags[id], t);

    case LET:
        t.let.value = evaluate(t.let.value);
        push(&ctx, t.let.name, t.let.value);
        t.let.body = evaluate(t.let.body);
        ctx.count--;
        return t.let.body;

    case AXIOM:
        push(&ctx, t.let.name, 0);
        t.let.body = evaluate(t.let.body);
        --ctx.count;
        return t.let.body;
        
    case CHECK:
        return evaluate(t.let.body);

    case ID: {
        int value = find(&ctx, t.id);

        if (value) {
            int id2 = alloc(value, tags[value], terms[value]);
            locations[id2] = locations[id];
            return id2;
        }

        return id;
    }

    case UNIVERSE:
    case NAME:
        return id;
    }
}

int eta_reduce(int id) {
    Term t = terms[id];
    if (tags[id] != LAM) return id;
        
    t.body = eta_reduce(t.body);
    Term b = terms[t.body];
        
    id = alloc(id, LAM, t);

    if (tags[t.body] != APP) return id;

    if (tags[b.arg] != ID || t.param != terms[b.arg].id) return id;
            
    if (!isfree(terms[b.arg].id, b.func)) return id;
                    
    return b.func;
}

int eq(int a, int b) {
    a = eta_reduce(a);
    b = eta_reduce(b);
    Term x = terms[a], y = terms[b];

    if (tags[a] != tags[b]) {
        goto fail;
    }

    switch (tags[a]) {
    case NAME:
        if (!strcmp(x.name, y.name)) return 1;
        goto fail;

    case ID:
        if (x.id == y.id) return 1;
        goto fail;

    case PI:
    case LAM:;
        if (!eq(x.type, y.type)) goto fail;
        Term p;
        p.id = x.param;
        int param = alloc(a, ID, p);
        y.body = subst_id(y.param, param, y.body);

        if (!eq(x.body, y.body)) return 0;
        return 1;
   
    case APP:
        if (!eq(x.func, y.func)) goto fail;
        if (!eq(x.arg, y.arg)) goto fail;
        return 1;

    case UNIVERSE:
        return 1;

    case LET:
        assert(0);
    }

fail:
    return 0;
}

const char *input;
int pos;

void print_loc(int loc) {
    int line = 1;
    int column = 1;

    int len = strlen(input);
    for (int i=0; i < loc && i < len; ++i) {
        if (input[i] == '\n') {
            line++;
            column = 1;
        } else {
            column++;
        }
    }
    
    printf("ERROR: on line %d, column %d:\n", line, column);
}

int recover_names(int id) {
    for (int i=global_bindings.count-1; i >= 0; --i) {
        if (eq(global_bindings.values[i], id)) {
            Term t = {0};
            t.name = symbols[global_bindings.names[i]];
            return alloc(global_bindings.names[i], NAME, t);
        }
    }

    Term t = terms[id];
    if (tags[id] & (LAM | PI)) {
        t.type = recover_names(t.type);
        t.body = recover_names(t.body);
    }

    if (tags[id] & APP) {
        t.func = recover_names(t.func);
        t.arg = recover_names(t.arg);
    }

    return alloc(id, tags[id], t);
}

void print_formatted_term(int id)
{
    print_term(recover_names(id));
}

void check_type_error(int ty, int value, int loc) {
    print_loc(loc);
    printf("Check statement is not correct, the value has type\n  ");
    print_formatted_term(term_types[value]);
    printf("\nand the expected type is\n  ");
    print_formatted_term(ty);
    printf("\n");

    longjmp(env, 1);
}

void let_type_error(int ty, int value, int loc) {
    print_loc(loc);
    printf("Trying to implement let binding with value type\n  ");
    print_formatted_term(term_types[value]);
    printf("\nwhen the declaration previously specified the type\n  ");
    print_formatted_term(ty);
    printf("\n");

    longjmp(env, 1);
}

void type_error(int fun, int arg, int loc) {
    print_loc(loc);
    printf("Trying to apply argument of type\n  ");
    print_formatted_term(term_types[arg]);
    printf("\nto a function that expected a\n  ");
    print_formatted_term(fun);
    printf("\n");

    longjmp(env, 1);
}

void undeclared_identifier_error(const char *name, int loc)
{
    print_loc(loc);
    printf("Undeclared identifier: '%s'\n", name);
    longjmp(env, 1);
}

void not_a_function_error(int fun, int arg, int loc)
{
    print_loc(loc);
    printf("Trying to apply argument '");
    print_formatted_term(arg);
    printf("' (which is a '");
    print_formatted_term(term_types[arg]);
    printf("') to '");
    print_formatted_term(fun);
    printf("' (which is not a function)\n");

    longjmp(env, 1);
}

int infer(int id) {
    Term t = terms[id];

    switch (tags[id]) {
    case NAME:
        undeclared_identifier_error(t.name, locations[id]);
       
    case ID:;
        int type = find(&type_ctx, t.id);

        if (!type) {
            undeclared_identifier_error(symbols[id], locations[id]);
        }

        id = evaluate(id);

        term_types[id] = type;
        return id;

    case LAM: {
        t.type = infer(t.type);

        int new_param = unique_id(id);
        t.body = subst_id(t.param, new_param, t.body);
        t.param = terms[new_param].id;

        push(&ctx, t.param, 0);
        push(&type_ctx, t.param, t.type);

        t.body = infer(t.body);

        type_ctx.count--;
        ctx.count--;

        id = alloc(id, LAM, t);

        Term ty = terms[id];
        ty.body = term_types[t.body];

        term_types[id] = alloc(id, PI, ty);
        return id;
    }

    case PI: {
        t.type = infer(t.type);

        push(&ctx, t.id, 0);
        push(&type_ctx, t.id, t.type);

        t.body = infer(t.body);

        type_ctx.count--;
        ctx.count--;

        id = alloc(id, PI, t);

        int ty = alloc(id, UNIVERSE, t);
        term_types[id] = ty;

        return id;
    }

    case UNIVERSE:
        term_types[id] = id;
        return id;

    case APP:
        int old_arg_location = locations[t.arg];
        t.arg = infer(t.arg);
        t.func = infer(t.func);

        if (tags[term_types[t.func]] != PI) {
            not_a_function_error(t.func, t.arg, old_arg_location);
        }

        Term f = terms[term_types[t.func]];

        if (!eq(term_types[t.arg], f.type)) {
            type_error(f.type, t.arg, locations[t.arg]);
        }

        push(&type_ctx, f.param, f.type);
        push(&ctx, f.param, t.arg);

        f.body = evaluate(f.body);

        type_ctx.count--;
        ctx.count--;

        id = evaluate(alloc(id, tags[id], t));
        term_types[id] = f.body;

        return id;

    case LET:;
        if (t.let.type)
            t.let.type = infer(t.let.type);
        t.let.value = infer(t.let.value);

        if (t.let.type && !eq(t.let.type, term_types[t.let.value])) {
            let_type_error(t.let.type, t.let.value, locations[t.let.value]);
        }

        push(&ctx, t.let.name, t.let.value);
        push(&type_ctx, t.let.name, term_types[t.let.value]);
        push(&global_bindings, id, t.let.value);

        t.let.body = infer(t.let.body);

        type_ctx.count--;
        ctx.count--;

        id = evaluate(alloc(id, LET, t));

        term_types[id] = term_types[t.let.body];
        return id;

    case AXIOM:
        t.let.type = infer(t.let.type);

        push(&ctx, t.let.name, 0);
        push(&type_ctx, t.let.name, t.let.type);

        t.let.body = infer(t.let.body);

        type_ctx.count--;
        ctx.count--;

        id = evaluate(alloc(id, AXIOM, t));

        term_types[id] = term_types[t.let.body];
        return id;

    case CHECK:
        t.let.type = infer(t.let.type);
        t.let.value = infer(t.let.value);

        if (!eq(t.let.type, term_types[t.let.value])) {
            check_type_error(t.let.type, t.let.value, locations[t.let.value]);
        }

        return infer(t.let.body);
    }
}

int subst_id(int name, int var, int id) {
    Term t = terms[id];

    switch (tags[id]) {
    case ID:
        if (t.id == name) {
            int id2 = alloc(var, tags[var], terms[var]);
            locations[id2] = locations[id];
            return id2;
        }
        return id;

    case NAME:
        return id;

    case PI:
    case LAM:
        if (t.type) t.type = subst_id(name, var, t.type);
        if (name == t.param) return alloc(id, tags[id], t);
        t.body = subst_id(name, var, t.body);
        break;

    case APP:
        t.func = subst_id(name, var, t.func);
        t.arg = subst_id(name, var, t.arg);
        break;

    case LET:
        if (t.let.type)
            t.let.type = subst_id(name, var, t.let.type);
        t.let.value = subst_id(name, var, t.let.value);
        t.let.body = subst_id(name, var, t.let.body);
        break;

    case AXIOM:
        t.let.type = subst_id(name, var, t.let.type);
        t.let.body = subst_id(name, var, t.let.body);
        break;

    case CHECK:
        t.let.type = subst_id(name, var, t.let.type);
        t.let.value = subst_id(name, var, t.let.value);
        t.let.body = subst_id(name, var, t.let.body);
        break;
    }
        
    return alloc(id, tags[id], t);
}

static char names[128*1024*1024];
int names_len = 0;

const char *parse_ident(void) {
    int old_pos = pos;

    if (input[pos] == '\'') ++pos;
    while (input[pos] && !isspace(input[pos]) &&
            input[pos] != ':' &&
            input[pos] != '[' &&
            input[pos] != ']' &&
            input[pos] != '{' &&
            input[pos] != '}' &&
            input[pos] != '(' &&
            input[pos] != ')' &&
            input[pos] != ';' &&
            input[pos] != ',' &&
            input[pos] != '\\' &&
            input[pos] != '%' &&
            input[pos] != '#')
    {
        ++pos;
    }
    while (pos > old_pos && input[pos-1] == '.') --pos;
    if (old_pos == pos) return 0;

    int len = pos - old_pos;
    char *name = names + names_len;
    memcpy(name, input + old_pos, len);
    name[len] = 0;
    names_len += len + 1;
    if (!strcmp(name, "->")) return 0;
    if (!strcmp(name, "=")) return 0;
    if (!strcmp(name, "#axiom")) return 0;
    if (!strcmp(name, "#check")) return 0;
 
    return name;
}

void parse_ws(void) {
    while (1) {
        if (!strncmp(&input[pos], "//", 2)) {
            while (input[pos] != '\n') ++pos;
            ++pos;
            continue;
        }
        if (!strncmp(&input[pos], "%", 1)) {
            while (input[pos] != '\n') ++pos;
            ++pos;
            continue;
        }
        if (!strncmp(&input[pos], "/*", 2)) {
            while (strncmp(&input[pos], "*/", 2)) ++pos;
            ++pos;
            ++pos;
            continue;
        }
        if (!(input[pos] == ' ' || input[pos] == '\n')) break;
        pos++;
    }
}

int parse_str(const char *str) {
    int len = strlen(str);

    parse_ws();
    if (!strncmp(input + pos, str, len)) {
        pos += len;
        parse_ws();
        return 1;
    }

    return 0;
}

int parse_term(void);
int parse_atom(void);
int parse_apps(void);

int parse_name(void) {
    int p = pos;
    Term t = {0};

    t.name = parse_ident();
    if (!t.name) return 0;

    if (!strcmp(t.name, "Type")) {
        int id = alloc(-1, UNIVERSE, t);
        locations[id] = p;
        return id;
    }

    int id = alloc(-1, NAME, t);
    symbols[id] = t.name;
    locations[id] = p;
    return id;
}

int subst_name(const char *name, int var, int id) {
    Term t = terms[id];

    switch (tags[id]) {
    case NAME:
        if (!strcmp(t.name, name)) {
            int id2 = alloc(var, tags[var], terms[var]);
            locations[id2] = locations[id];
            return id2;
        }
        return id;

    case UNIVERSE:
    case ID:
        return id;

    case PI:
    case LAM:
        if (t.type) t.type = subst_name(name, var, t.type);
        if (t.param == terms[var].id) return 0;
        t.body = subst_name(name, var, t.body);
        break;

    case APP:
        t.func = subst_name(name, var, t.func);
        t.arg = subst_name(name, var, t.arg);
        break;

    case LET:
        if (t.let.type)
            t.let.type = subst_name(name, var, t.let.type);
        t.let.value = subst_name(name, var, t.let.value);
        t.let.body = subst_name(name, var, t.let.body);
        break;

    case AXIOM:
        t.let.type = subst_name(name, var, t.let.type);
        t.let.body = subst_name(name, var, t.let.body);
        break;

    case CHECK:
        t.let.type = subst_name(name, var, t.let.type);
        t.let.value = subst_name(name, var, t.let.value);
        t.let.body = subst_name(name, var, t.let.body);
        break;
    }
        
    return alloc(id, tags[id], t);
}

void integerize(const char *param_name, int *body, int *param) {
    *param = unique++;

    Term param_var = {0};
    param_var.id = *param;

    int param_term = alloc(-1, ID, param_var);
    symbols[param_term] = param_name;

    *body = subst_name(param_name, param_term, *body);
}

int parse_anon_pi(void) {
    int p = pos;
    Term t = {0};

    t.type = parse_apps();
    if (!t.type) return 0;

    if (!parse_str("->")) return t.type;

    t.body = parse_term();
    if (!t.body) {
        print_loc(pos);
        printf("Failed to parse due to a malformed function type body\n");
        longjmp(env, 1);
    }

    const char *param_name = "_";
    integerize(param_name, &t.body, &t.param);
    int id = alloc(-1, PI, t);
    symbols[id] = param_name;
    locations[id] = p;
    return id;
}

int parse_pi(void) {
    int p = pos;
    Term t = {0};

    if (!parse_str("(")) return 0;

    const char *param_name = parse_ident();
    if (!param_name) {
        return 0;
    }

    if (!parse_str(":")) return 0;

    t.type = parse_term();
    assert(t.type);

    if (!parse_str(")")) return 0;

    if (!parse_str("->")) {
        print_loc(pos);
        printf("Failed to parse, function types use '->' after the parameter\n");
        longjmp(env, 1);
    }

    t.body = parse_term();
    assert(t.body);

    integerize(param_name, &t.body, &t.param);
    int id = alloc(-1, PI, t);
    symbols[id] = param_name;
    locations[id] = p;
    return id;
}

int parse_lam(void) {
    int p = pos;
    Term t = {0};

    if (!parse_str("\\")) return 0;

    const char *param = parse_ident();
    if (!param) {
        print_loc(pos);
        printf("Failed to parse the lambda abstraction, since it's missing the parameter name\n");
        longjmp(env, 1);
    }

    if (!parse_str(":")) {
        print_loc(pos);
        printf("Failed to parse the lambda abstraction, a ':' is expected after the parameter name\n");
        longjmp(env, 1);
    }

    t.type = parse_term();
    assert(t.type);

    if (!parse_str(".")) {
        print_loc(pos);
        printf("Failed to parse, lambdas use a '.' after the parameter type to delimit the body\n");
        longjmp(env, 1);
    }

    t.body = parse_term();
    assert(t.body);

    integerize(param, &t.body, &t.param);
    int id = alloc(-1, LAM, t);
    symbols[id] = param;
    locations[id] = p;

    return id;
}

int parse_let(void) {
    int p = pos;

    const char *param_name = parse_ident();
    if (!param_name) {
        return 0;
    }

    int type = 0;

    if (!parse_str("=")) {
        return 0;
    }

    int value = parse_term();
    assert(value);

    if (!parse_str(";")) {
        print_loc(pos);
        printf("Failed to parse the end of the let binding, expected a ';' as the final delimiter\n");
        longjmp(env, 1);
    }

    Term t = {0};

    int body;

    parse_ws();
    if (!input[pos]) {
        body = alloc(-1, UNIVERSE, t);
    } else {
        body = parse_term();
        assert(body);
    }

    integerize(param_name, &body, &t.let.name);

    t.let.type = type;
    t.let.value = value;
    t.let.body = body;

    int id = alloc(-1, LET, t);

    symbols[id] = param_name;
    locations[id] = p;

    return id;
}

int parse_check(void) {
    int p = pos;

    if (!parse_str("#check")) {
        return 0;
    }

    int value = parse_term();
    assert(value);

    if (!parse_str(":")) {
        print_loc(pos);
        printf("Failed to parse the check statement, expected a ':' after the value\n");
        longjmp(env, 1);
    }

    int type = parse_term();
    assert(type);

    if (!parse_str(";")) {
        print_loc(pos);
        printf("Failed to parse the end of the check statement, expected a ';' after the type\n");
        longjmp(env, 1);
    }

    int body = parse_term();
    assert(body);

    Term t = {0};
    t.let.type = type;
    t.let.value = value;
    t.let.body = body;

    int id = alloc(-1, CHECK, t);

    locations[id] = p;

    return id;
}

int parse_axiom(void) {
    int p = pos;

    if (!parse_str("#axiom")) {
        return 0;
    }

    const char *param_name = parse_ident();
    if (!param_name) {
        print_loc(pos);
        printf("Failed to parse the axiom declaration since its name is missing\n");
        longjmp(env, 1);
    }

    if (!parse_str(":")) {
        print_loc(pos);
        printf("Failed to parse the axiom declaration, the type must be specified after a ':'\n");
        longjmp(env, 1);
    }

    int type = parse_term();
    assert(type);

    if (!parse_str(";")) {
        print_loc(pos);
        printf("Failed to parse the end of the axiom declaration, expected a ';' as the final delimiter\n");
        longjmp(env, 1);
    }

    parse_ws();
    if (!input[pos]) {
        print_loc(pos);
        printf("Failed to parse program, missing final expression at the end of declarations\n");
        longjmp(env, 1);
    }

    int body = parse_term();
    assert(body);

    Term t = {0};
    integerize(param_name, &body, &t.let.name);

    t.let.type = type;
    t.let.body = body;

    int id = alloc(-1, AXIOM, t);

    symbols[id] = param_name;
    locations[id] = p;

    return id;
}

int parse_apps(void) {
    int p = pos;
    Term t = {0};

    t.func = parse_atom();
    if (!t.func) return 0;
     
    while (1) {
        parse_ws();
        
        int tag = APP;

        int p2 = pos;

        t.arg = parse_atom();
        if (!t.arg) break;

        t.func = alloc(-1, tag, t);
        locations[t.func] = p;
    }

    return t.func;
}

int parse_paren(void) {
    int p = pos;
    int id;
    if (!parse_str("(")) return 0;

    id = parse_term();
    assert(id);

    if (!parse_str(")")) {
        print_loc(pos);
        printf("Failed to parse expression due to missing ')'\n");
        longjmp(env, 1);
    }

    locations[id] = p;
    return id;
}

int parse_term(void) {
    int id, old_pos = pos;

    id = parse_pi();
    if (id) return id;
    pos = old_pos;

    id = parse_lam();
    if (id) return id;
    pos = old_pos;

    id = parse_axiom();
    if (id) return id;
    pos = old_pos;

    id = parse_check();
    if (id) return id;
    pos = old_pos;

    id = parse_let();
    if (id) return id;
    pos = old_pos;

    id = parse_anon_pi();
    if (id) return id;

    print_loc(pos);
    printf("Failed to parse expression due to malformed syntax\n");
    longjmp(env, 1);
}

int parse_atom(void) {
    int id, old_pos = pos;

    id = parse_name();
    if (id) return id;
    pos = old_pos;

    return parse_paren();
}

int main(int argc, char **argv) {
    FILE *f;
    if (argc <= 1) {
        printf("Expected input file path\n");
        return 1;
    }

    terms = malloc(sizeof(*terms) * MAX_TERMS);
    term_types = malloc(sizeof(*term_types) * MAX_TERMS);

    tags = malloc(sizeof(*tags) * MAX_TERMS);
    locations = malloc(sizeof(*locations) * MAX_TERMS);
    symbols = malloc(sizeof(*symbols) * MAX_TERMS);


    static char outbuf[1024*1024];
    if (setvbuf(stdout, outbuf, _IOFBF, 1024*1024) != 0) {
        return 1;
    }
    char *filename=argv[1];
        
    printf("\x1b[?25l");

    int frame = 0;

    char lbuf[16*2048];
    int len = 0;

    int v,t;
    char dots[20];
    memset(dots, ' ', 20);
    for (int i = 0; i < 4; ++i) dots[i] = '~';

    while (1) {
        LARGE_INTEGER freq, begin_time, end_time;
        double elapsed_time;
        QueryPerformanceFrequency(&freq);
        QueryPerformanceCounter(&begin_time);

        terms_count = 1;
        names_len = 0;
        names[0] = 0;
        ctx.count = 0;
        type_ctx.count = 0;
        global_bindings.count = 0;
             fflush(stdout);

        //Sleep(0.5);

        printf("\x1b[H");
        printf("\x1b[2J");
/*
        printf("\n");
        for (int i = 20; i >= 0; --i) printf("%c", dots[(i + frame/10) % 20]);
        ++frame;
        printf("\n");*/


        int value = _setjmp(env); 
        if (value == 0) {
            f = fopen(filename, "r+");
            if (!f) goto end;
            len = fread(lbuf, 1, sizeof(lbuf), f);
            fclose(f);

            lbuf[len]=0;

            input = lbuf;
            pos = 0;
            parse_ws();

            v = parse_term();

            if (!v) {
                printf("Failed to parse contents\n");
                continue;
            }

            parse_ws();
            if (input[pos]) {
                printf("Leftover input\n");
                continue;
            }
           
            v=infer(v);
             t = term_types[v];

          //      }
         //   }

            printf("\nFinished typechecking and evaluation.\n");

            printf("\n");
            printf("Resulting term: ");
            print_term(v);
            printf("\nwhich has type: ");
            print_term(t);
            printf("\n");
        }

        QueryPerformanceCounter(&end_time);
        elapsed_time = (double)(end_time.QuadPart - begin_time.QuadPart) / freq.QuadPart;

        //printf("Total time spent: %lf ms\n", elapsed_time * 1000.0);
end:;

    }
}

