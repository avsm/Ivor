#include "closure.h"
#include <stdio.h>

#define FPLUS1 10
#define FPLUS2 20
#define ADDER1 40
#define ADDER 50

#define FTAG_EVM_plus 1
VAL _EVM_plus(VAL v0,VAL v1);
#define FTAG_EVMSC_1_plus 2
VAL _EVMSC_1_plus(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_plus 3
VAL _EVMSC_0_plus(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_natElim 0
VAL _EVM_natElim(VAL v0,VAL v1,VAL v2,VAL v3);


VAL plus2(VAL k, VAL ih);
VAL adder1(VAL n,VAL a, VAL k);
VAL adder(VAL n, VAL a);


VAL eval(VAL x) {
    if (x->ty != FUN) return x;
    else {
	function* f = (function*)(x -> info);
	switch(f->ftag) {
	    EVALCASE(FPLUS2,2,plus2(FARG(0),FARG(1)));
	    EVALCASE(ADDER1,3,adder1(FARG(0),FARG(1),FARG(2)));
	    EVALCASE(ADDER,2,adder(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_plus,2,_EVM_plus(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_plus,4,_EVMSC_1_plus(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_plus,3,_EVMSC_0_plus(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_natElim,4,_EVM_natElim(FARG(0),FARG(1),FARG(2),FARG(3)));
	    EVALDEFAULT;
	}
    }
    return x;
}

VAL natElim(VAL n, VAL P, VAL mz, VAL ms) {
    switch(TAG(eval(n))) {
    case 0:
	return mz;
	break;
    case 1:
	return eval(CLOSUREADD2(ms, GETCONARG(n,0), 
			   natElim(GETCONARG(n,0), P, mz, ms)));
	break;
    default:
	return NULL;
    }
}

VAL plus1(VAL n) {
    return MKTYPE;
}

VAL plus2(VAL k, VAL ih) {
    return MKCON1(1,ih);
}

VAL plus(VAL m, VAL n) {
    return natElim(m,CLOSURE0(FPLUS1,1),n,CLOSURE0(FPLUS2,2));
}

VAL adder1(VAL n,VAL a, VAL k) {
    return adder(GETCONARG(n,0),_EVM_plus(a,k));
}

VAL adder(VAL n, VAL a)
{
    switch(TAG(eval(n))) {
    case 0:
	return a;
	break;
    case 1:
	return CLOSURE2(ADDER1,3,n,a);
    default:
	return NULL;
    }
}

void shownat(VAL f) {
    switch(f->ty) {
    case FUN:
	printf("FUN %d %d",((function*)(f->info))->ftag,((function*)(f->info))->next);
	break;
    case CON:
	if (TAG(f)==0) printf("O");
	if (TAG(f)==1) {
	    printf("S");
	    shownat(GETCONARG(f,0));
	}
	break;
    case TYPE:
	printf("TYPE");
    }
}


VAL _EVM_plus(VAL v0,VAL v1) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL* args;
    tmp1 = v1;
    tmp3 = v0;
    tmp4 = v1;
    tmp2 = CLOSURE2(FTAG_EVMSC_0_plus,3,tmp3,tmp4);
    tmp3 = v0;
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_1_plus,4,tmp5,tmp6);
    return _EVM_natElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_plus(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v3;
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_0_plus(VAL v0,VAL v1,VAL v2) {

    VAL* args;
    VAL tmp0;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_natElim(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    eval(v0);
    switch(TAG(v0)) {
    case 0:
    tmp0 = v2;
    return tmp0;

    case 1:
    tmp1 = v3;
    tmp3 = v0;
    tmp2 = GETCONARG(tmp3,0);
    tmp5 = v0;
    tmp4 = GETCONARG(tmp5,0);
    tmp5 = v1;
    tmp6 = v2;
    tmp7 = v3;
    tmp3 = _EVM_natElim(tmp4,tmp5,tmp6,tmp7);
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    eval(tmp0);
    return tmp0;

    default:
    return NULL;
    }
}

int main()
{
    VAL f;
    VAL one;
    VAL two;
    VAL three;
    VAL four;

    VAL tmp;
    VAL* args;

    VM_init();

    one = MKCON1(1,MKCON0(0));
    two = MKCON1(1,one);
    three = MKCON1(1,two);
    four = MKCON1(1,three);

    args = MKARGS(6);
    args[0] = four;
    args[1] = two;
    args[2] = four;
    args[3] = two;
    args[4] = four;
    args[5] = three;

    tmp = CLOSUREN(ADDER,6,args,6);
//    tmp = _EVM_plus(two,two);
    shownat(tmp);
    printf("\n");

//    tmp = CLOSUREADD1(tmp,three);
//    shownat(tmp);
//    printf("\n");

//    tmp = eval(CLOSUREADD1(tmp,two));

    shownat(eval(tmp));
    printf("\n");

    return 0;
}
