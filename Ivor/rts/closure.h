#ifndef _CLOSURE_H
#define _CLOSURE_H

#include <gc/gc.h>

typedef enum { FUN, CON, TYPE } closure_type;

// Simulate a let x = y in z binding.
// This works because x=y evaluates to y, and y will always be non-null.
// More generally, we could have #define LET(x,y,z) (((x=y) || 1) ? (z) : 0)
#define LET(x,y,z) ((x=y) ? (z) : (VAL)0)

typedef struct {
    closure_type ty;
    void* info;
} closure ;

typedef closure* VAL;


typedef struct {
    int ftag; // Function tag
    int space; // How much space for arguments
    int next; // Where to put the next argument
    closure** args;
} function;

typedef struct {
    int tag;
    closure** args;
} constructor;

/// If we ever need a value we're not going to examine... Types, say.
extern VAL DontCare;

/// Set everything up. Call this before doing anything.
void VM_init();

/// Having all these looks horrible, but it's for the sake of efficiency.
closure* CLOSURE0(int ftag, int argspace);
closure* CLOSURE1(int ftag, int argspace,closure* val);
closure* CLOSURE2(int ftag, int argspace,closure* val, closure* val2);
closure* CLOSURE3(int ftag, int argspace,closure* val, closure* val2,
		  closure* val3);
closure* CLOSURE4(int ftag, int argspace,closure* val, closure* val2,
		  closure* val3, closure* val4);
closure* CLOSURE5(int ftag, int argspace,closure* val, closure* val2,
		  closure* val3, closure* val4, closure* val5);
closure* CLOSUREADD1(closure* fn, closure* val);
closure* CLOSUREADD2(closure* fn, closure* val, closure* val2);
closure* CLOSUREADD3(closure* fn, closure* val, closure* val2, closure* val3);
closure* CLOSUREADD4(closure* fn, closure* val, closure* val2, closure* val3,
		     closure* val4);
closure* CLOSUREADD5(closure* fn, closure* val, closure* val2, closure* val3,
		     closure* val4, closure* val5);

/// Less efficient ones for bigger cases (5 should usually be enough)
closure* CLOSUREN(int ftag, int argspace, closure** args, int argsleft);
closure* CLOSUREADDN(closure* fn, closure** args,int argsleft);


closure* MKCON0(int tag);
closure* MKCON1(int tag,closure* val);

closure* MKCONN(int tag,closure** args,int argsleft);

#define MKVAL (closure*)GC_MALLOC(sizeof(closure))
#define MKFUN (function*)GC_MALLOC(sizeof(function))
#define MKCON (constructor*)GC_MALLOC(sizeof(constructor))
#define MKTYPE DontCare
#define MKARGS(x) (closure**)GC_MALLOC(sizeof(closure)*x);
#define MOREARGS(args,x) (closure**)GC_REALLOC(args,sizeof(closure)*x);

#define GETFUNARG(c,x) ((function*)(c->info))->args[x]
#define GETCONARG(c,x) ((constructor*)(c->info))->args[x]
#define TAG(c) ((constructor*)(c->info))->tag

#define FARG(x) eval(f->args[x])

// Do some magic
#define EVALCASE(fntag,arity,fn) \
case fntag: \
if (f->next==arity) { \
    x=fn; \
} else { \
    if (f->next>arity) { \
	x=eval(CLOSUREADDN(fn,f->args+arity,f->next-arity)); \
    } \
} \
break

#define EVALDEFAULT default: printf("Nothing happens\n"); return x



#endif // Whole file
