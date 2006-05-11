#include "closure.h"
#include <stdio.h>

VAL DontCare;

extern VAL eval(VAL x);

void VM_init()
{
    DontCare = MKVAL;
    DontCare->ty = TYPE;
    DontCare->info = NULL;
}

void showclosure(VAL f) {
    switch(f->ty) {
    case FUN:
	printf("FUN %d %d",((function*)(f->info))->ftag,((function*)(f->info))->next);
	break;
    case CON:
	printf("CON %d",TAG(f));
	break;
    case TYPE:
	printf("TYPE");
	break;
    }
}

closure* CLOSURE0(int ftag, int argspace)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 0;
    f->args = MKARGS(argspace);
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSURE1(int ftag, int argspace, closure* val)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 1;
    f->args = MKARGS(argspace);
    f->args[0] = val;
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSURE2(int ftag, int argspace, closure* val, closure* val2)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 2;
    f->args = MKARGS(argspace);
    f->args[0] = val;
    f->args[1] = val2;
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSURE3(int ftag, int argspace, closure* val, closure* val2,
		  closure* val3)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 3;
    f->args = MKARGS(argspace);
    f->args[0] = val;
    f->args[1] = val2;
    f->args[2] = val3;
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSURE4(int ftag, int argspace, closure* val, closure* val2,
		  closure* val3, closure* val4)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 4;
    f->args = MKARGS(argspace);
    f->args[0] = val;
    f->args[1] = val2;
    f->args[2] = val3;
    f->args[3] = val4;
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSURE5(int ftag, int argspace, closure* val, closure* val2,
		  closure* val3, closure* val4, closure* val5)
{
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = 5;
    f->args = MKARGS(argspace);
    f->args[0] = val;
    f->args[1] = val2;
    f->args[2] = val3;
    f->args[3] = val4;
    f->args[4] = val5;
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

closure* CLOSUREN(int ftag, int argspace, closure** args, int argsleft)
{
    int i;
    closure* v = MKVAL;
    function* f = MKFUN;
    f->ftag = ftag;
    f->space = argspace;
    f->next = argsleft;
    f->args = MKARGS(argspace);
    i=0;
    while(argsleft>0) {
	f->args[i] = args[i];
	i++;
	argsleft--;
    }
    v->ty = FUN;
    v->info=(void*)f;
    return eval(v);
}

function* copyFunction(function* f)
{
    function* fnew;
    int i;

    fnew = MKFUN;
    fnew->ftag = f->ftag;
    fnew->space = f->space;
    fnew->next = f->next;
    fnew->args = MKARGS(f->next);
    for(i=0;i<f->next;i++) {
	fnew->args[i] = f->args[i];
    }
    return fnew;
}

closure* copyClosure(closure* c)
{
    closure* cnew;
    cnew = MKVAL;
    cnew->ty = c->ty;
    switch(c->ty) {
    case FUN:
	cnew->info = (void*)copyFunction((function*)c->info);
	break;
    case CON:
	cnew->info = c->info;
	break;
    case TYPE:
	cnew->info = NULL;
    }
    return cnew;
}

closure* CLOSUREADD1(closure* fn, closure* val)
{
    int next;
    closure* c = copyClosure(fn);
    function* f = (function*)(c -> info);
    if (f->next+1>f->space) {
	// We have all the arguments we need, so this doesn't make sense...
	f->args = MOREARGS(f->args,f->next+1);
	f->space = f->next+1;
    }
    next = f->next;
    f->args[next] = val;
    f->next+=1;
    return eval(c);
}

closure* CLOSUREADD2(closure* fn, closure* val, closure* val2)
{
    int next;
    closure* c = copyClosure(fn);
    function* f = (function*)(c -> info);
    if (f->next+2>f->space) {
	f->args = MOREARGS(f->args,f->next+2);
	f->space = f->next+2;
    }
    next = f->next;
    f->args[next] = val;
    f->args[next+1] = val2;
    f->next+=2;
    return eval(c);
}

closure* CLOSUREADD3(closure* fn, closure* val, closure* val2,
		     closure* val3)
{
    int next;
    closure* c = copyClosure(fn);
    function* f = (function*)(c -> info);
    if (f->next+3>f->space) {
	f->args = MOREARGS(f->args,f->next+3);
	f->space = f->next+3;
    }
    next = f->next;
    f->args[next] = val;
    f->args[next+1] = val2;
    f->args[next+2] = val3;
    f->next+=3;
    return eval(c);
}

closure* CLOSUREADD4(closure* fn, closure* val, closure* val2,
		     closure* val3, closure* val4)
{
    int next;
    closure* c = copyClosure(fn);
    function* f = (function*)(c -> info);
    if (f->next+4>f->space) {
	f->args = MOREARGS(f->args,f->next+4);
	f->space = f->next+4;
    }
    next = f->next;
    f->args[next] = val;
    f->args[next+1] = val2;
    f->args[next+2] = val3;
    f->args[next+3] = val4;
    f->next+=4;
    return eval(c);
}

closure* CLOSUREADD5(closure* fn, closure* val, closure* val2,
		     closure* val3, closure* val4, closure* val5)
{
    int next;
    closure* c = copyClosure(fn);
    function* f = (function*)(c -> info);
    if (f->next+5>f->space) {
	f->args = MOREARGS(f->args,f->next+5);
	f->space = f->next+5;
    }
    next = f->next;
    f->args[next] = val;
    f->args[next+1] = val2;
    f->args[next+2] = val3;
    f->args[next+3] = val4;
    f->args[next+4] = val5;
    f->next+=5;
    return eval(c);
}

closure* MKCON0(int tag)
{
    closure* v = MKVAL;
    constructor* c = MKCON;
    c->tag = tag;
    c->args = NULL;
    v->ty = CON;
    v->info=(void*)c;
    return v;
}

/*
  tmpv = MKVAL;
  tmpc = MKCON;
  tmpc->tag = tag; tmpc->args=MKARGS(1); tmpc->args[0]=val;
  tmpv->ty=CON->
 */

closure* MKCON1(int tag,closure* val)
{
    closure* v = MKVAL;
    constructor* c = MKCON;
    c->tag = tag;
    c->args = MKARGS(1);
    c->args[0] = val;
    v->ty = CON;
    v->info=(void*)c;
    return v;
}

closure* MKCONN(int tag,closure** args,int argsleft)
{
    int i;
    closure* v = MKVAL;
    constructor* c = MKCON;
    c->tag = tag;
    c->args = MKARGS(argsleft);
    i=0;
    while(argsleft>0) {
	c->args[i] = args[i];
	i++;
	argsleft--;
    }
    v->ty = CON;
    v->info=(void*)c;
    return v;
}

// Apply the unused arguments to the closure fn
closure* CLOSUREADDN(closure* v, closure** args,int argsleft)
{
    while(argsleft>0) {
	switch(argsleft) {
	case 5:
	    v=CLOSUREADD5(v,*args,*(args+1),*(args+2),
			  *(args+3),*(args+4));
	    args+=5;
	    argsleft-=5;
	    break;
	case 4:
	    v=CLOSUREADD4(v,*args,*(args+1),*(args+2),
			  *(args+3));
	    args+=4;
	    argsleft-=4;
	    break;
	case 3:
	    v=CLOSUREADD3(v,*args,*(args+1),*(args+2));
	    args+=3;
	    argsleft-=3;
	    break;
	case 2:
	    v=CLOSUREADD2(v,*args,*(args+1));
	    args+=2;
	    argsleft-=2;
	    break;
	default:
	    // Slow way
	    if (argsleft>5) {
		v=CLOSUREADD5(v,*args,*(args+1),*(args+2),
			      *(args+3),*(args+4));
		args+=5;
		argsleft-=5;
	    }
	    else {
		v=CLOSUREADD1(v,*(args++));
		--argsleft;
	    }
	}
    }
    return v;
}
