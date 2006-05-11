#include "closure.h"
#include <stdio.h>

#define FTAG_EVM_vectFold 11
VAL _EVM_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_1_vectFold 12
VAL _EVMSC_1_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8,VAL v9);
#define FTAG_EVMSC_0_vectFold 13
VAL _EVMSC_0_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVM_VectElim 10
VAL _EVM_VectElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVM_fact 7
VAL _EVM_fact(VAL v0);
#define FTAG_EVMSC_1_fact 8
VAL _EVMSC_1_fact(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_fact 9
VAL _EVMSC_0_fact(VAL v0,VAL v1);
#define FTAG_EVM_mult 4
VAL _EVM_mult(VAL v0,VAL v1);
#define FTAG_EVMSC_1_mult 5
VAL _EVMSC_1_mult(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_mult 6
VAL _EVMSC_0_mult(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_plus 1
VAL _EVM_plus(VAL v0,VAL v1);
#define FTAG_EVMSC_1_plus 2
VAL _EVMSC_1_plus(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_plus 3
VAL _EVMSC_0_plus(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_natElim 0
VAL _EVM_natElim(VAL v0,VAL v1,VAL v2,VAL v3);

VAL eval(VAL x) {
    if (x->ty != FUN) return x;
    else {
        function* f = (function*)(x -> info);
        switch(f->ftag) {
            EVALCASE(FTAG_EVM_vectFold,6,_EVM_vectFold(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_1_vectFold,10,_EVMSC_1_vectFold(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7),FARG(8),FARG(9)));
            EVALCASE(FTAG_EVMSC_0_vectFold,8,_EVMSC_0_vectFold(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVM_VectElim,6,_EVM_VectElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVM_fact,1,_EVM_fact(FARG(0)));
            EVALCASE(FTAG_EVMSC_1_fact,3,_EVMSC_1_fact(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_fact,2,_EVMSC_0_fact(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_mult,2,_EVM_mult(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_mult,4,_EVMSC_1_mult(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_mult,3,_EVMSC_0_mult(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_plus,2,_EVM_plus(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_plus,4,_EVMSC_1_plus(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_plus,3,_EVMSC_0_plus(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_natElim,4,_EVM_natElim(FARG(0),FARG(1),FARG(2),FARG(3)));
        }
    }
    return x;
}

VAL _EVM_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp12;
    VAL tmp11;
    VAL tmp10;
    VAL tmp9;
    VAL tmp8;
    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp2 = v2;
    tmp3 = v3;
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp8 = v3;
    tmp9 = v4;
    tmp10 = v5;
    args = MKARGS(6);
    args[0] = tmp5;
    args[1] = tmp6;
    args[2] = tmp7;
    args[3] = tmp8;
    args[4] = tmp9;
    args[5] = tmp10;
    tmp4 = CLOSUREN(FTAG_EVMSC_0_vectFold,6,args,6);
    tmp5 = v4;
    tmp7 = v0;
    tmp8 = v1;
    tmp9 = v2;
    tmp10 = v3;
    tmp11 = v4;
    tmp12 = v5;
    args = MKARGS(6);
    args[0] = tmp7;
    args[1] = tmp8;
    args[2] = tmp9;
    args[3] = tmp10;
    args[4] = tmp11;
    args[5] = tmp12;
    tmp6 = CLOSUREN(FTAG_EVMSC_1_vectFold,6,args,6);
    return _EVM_VectElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_1_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8,VAL v9) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v5;
    tmp2 = v7;
    tmp3 = v9;
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;
}

VAL _EVMSC_0_vectFold(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp0;
    VAL* args;
    tmp0 = v1;
    return tmp0;
}

VAL _EVM_VectElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp11;
    VAL tmp10;
    VAL tmp9;
    VAL tmp8;
    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    eval(v2);
    switch(TAG(v2)) {
    case 0:
    tmp0 = v4;
    return tmp0;

    case 1:
    tmp1 = v5;
    tmp3 = v2;
    tmp2 = GETCONARG(tmp3,1);
    tmp4 = v2;
    tmp3 = GETCONARG(tmp4,2);
    tmp5 = v2;
    tmp4 = GETCONARG(tmp5,3);
    tmp7 = v2;
    tmp6 = GETCONARG(tmp7,0);
    tmp8 = v2;
    tmp7 = GETCONARG(tmp8,1);
    tmp9 = v2;
    tmp8 = GETCONARG(tmp9,3);
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    tmp5 = _EVM_VectElim(tmp6,tmp7,tmp8,tmp9,tmp10,tmp11);
    tmp0 = CLOSUREADD4(tmp1,tmp2,tmp3,tmp4,tmp5);
    return tmp0;

    default:
    return NULL;
    }
}

VAL _EVM_fact(VAL v0) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp2 = CLOSURE1(FTAG_EVMSC_0_fact,1,tmp3);
    tmp4 = MKCON0(0);
    tmp3 = MKCON1(1,tmp4);
    tmp5 = v0;
    tmp4 = CLOSURE1(FTAG_EVMSC_1_fact,1,tmp5);
    return _EVM_natElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_fact(VAL v0,VAL v1,VAL v2) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v1;
    tmp1 = MKCON1(1,tmp2);
    tmp2 = v2;
    return _EVM_mult(tmp1,tmp2);
}

VAL _EVMSC_0_fact(VAL v0,VAL v1) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_mult(VAL v0,VAL v1) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp3 = v0;
    tmp4 = v1;
    tmp2 = CLOSURE2(FTAG_EVMSC_0_mult,2,tmp3,tmp4);
    tmp3 = MKCON0(0);
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_1_mult,2,tmp5,tmp6);
    return _EVM_natElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_mult(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp2 = v3;
    return _EVM_plus(tmp1,tmp2);
}

VAL _EVMSC_0_mult(VAL v0,VAL v1,VAL v2) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_plus(VAL v0,VAL v1) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp3 = v0;
    tmp4 = v1;
    tmp2 = CLOSURE2(FTAG_EVMSC_0_plus,2,tmp3,tmp4);
    tmp3 = v0;
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_1_plus,2,tmp5,tmp6);
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

    VAL tmp0;
    VAL* args;
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
    return tmp0;

    default:
    return NULL;
    }
}

