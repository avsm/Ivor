#include "closure.h"
#include <stdio.h>

#define FTAG_EVM_testval 5
VAL _EVM_testval();
#define FTAG_EVM_plus 1
VAL _EVM_plus(VAL v0);
#define FTAG_EVMSC_2_plus 2
VAL _EVMSC_2_plus(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_1_plus 3
VAL _EVMSC_1_plus(VAL v0,VAL v1);
#define FTAG_EVMSC_0_plus 4
VAL _EVMSC_0_plus(VAL v0,VAL v1);
#define FTAG_EVM_NatElim 0
VAL _EVM_NatElim(VAL v0,VAL v1,VAL v2,VAL v3);
VAL eval(VAL x) {
    if (x->ty != FUN) return x;
    else {
        function* f = (function*)(x -> info);
        switch(f->ftag) {
            EVALCASE(FTAG_EVM_testval,0,_EVM_testval());
            EVALCASE(FTAG_EVM_plus,1,_EVM_plus(FARG(0)));
            EVALCASE(FTAG_EVMSC_2_plus,4,_EVMSC_2_plus(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_1_plus,2,_EVMSC_1_plus(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_0_plus,2,_EVMSC_0_plus(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_NatElim,4,_EVM_NatElim(FARG(0),FARG(1),FARG(2),FARG(3)));
        }
    }
    return x;
}
VAL _EVM_testval() {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp5 = MKCON0(0);
    tmp4 = MKCON1(1,tmp5);
    tmp3 = MKCON1(1,tmp4);
    tmp2 = MKCON1(1,tmp3);
    tmp1 = MKCON1(1,tmp2);
    tmp6 = MKCON0(0);
    tmp5 = MKCON1(1,tmp6);
    tmp4 = MKCON1(1,tmp5);
    tmp3 = MKCON1(1,tmp4);
    tmp2 = MKCON1(1,tmp3);
    tmp0 = CLOSURE2(FTAG_EVM_plus,2,tmp1,tmp2);
    return tmp0;
}

VAL _EVM_plus(VAL v0) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp2 = CLOSURE1(FTAG_EVMSC_0_plus,1,tmp3);
    tmp4 = v0;
    tmp3 = CLOSURE1(FTAG_EVMSC_1_plus,1,tmp4);
    tmp5 = v0;
    tmp4 = CLOSURE1(FTAG_EVMSC_2_plus,1,tmp5);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_2_plus(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v2;
    tmp3 = v3;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_1_plus(VAL v0,VAL v1) {

    VAL tmp0;
    VAL* args;
    tmp0 = v1;
    return tmp0;
}

VAL _EVMSC_0_plus(VAL v0,VAL v1) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_NatElim(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp3 = _EVM_NatElim(tmp4,tmp5,tmp6,tmp7);
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;

    default:
    return NULL;
    }
}

