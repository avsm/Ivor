#include "closure.h"
#include <stdio.h>

#define FTAG_EVM_testval 104
VAL _EVM_testval();
#define FTAG_EVM_testvect2 103
VAL _EVM_testvect2();
#define FTAG_EVM_vectsum 100
VAL _EVM_vectsum(VAL v0,VAL v1);
#define FTAG_EVMSC_1_vectsum 101
VAL _EVMSC_1_vectsum(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_0_vectsum 102
VAL _EVMSC_0_vectsum(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_testvect 99
VAL _EVM_testvect();
#define FTAG_EVM_vtail 98
VAL _EVM_vtail(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_vtailAux 93
VAL _EVM_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_2_vtailAux 94
VAL _EVMSC_2_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8);
#define FTAG_EVMSC_3_vtailAux 95
VAL _EVMSC_3_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8,VAL v9);
#define FTAG_EVMSC_1_vtailAux 96
VAL _EVMSC_1_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_0_vtailAux 97
VAL _EVMSC_0_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVM_FinElim 92
VAL _EVM_FinElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVM_VectElim 91
VAL _EVM_VectElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVM_plus_eq_fst_sym 88
VAL _EVM_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_1_plus_eq_fst_sym 89
VAL _EVMSC_1_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_plus_eq_fst_sym 90
VAL _EVMSC_0_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_plus_eq_fst 78
VAL _EVM_plus_eq_fst(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_2_plus_eq_fst 79
VAL _EVMSC_2_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_8_plus_eq_fst 80
VAL _EVMSC_8_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8);
#define FTAG_EVMSC_7_plus_eq_fst 81
VAL _EVMSC_7_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_6_plus_eq_fst 82
VAL _EVMSC_6_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_5_plus_eq_fst 83
VAL _EVMSC_5_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8);
#define FTAG_EVMSC_4_plus_eq_fst 84
VAL _EVMSC_4_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_3_plus_eq_fst 85
VAL _EVMSC_3_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_1_plus_eq_fst 86
VAL _EVMSC_1_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_plus_eq_fst 87
VAL _EVMSC_0_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_plus_assoc 65
VAL _EVM_plus_assoc(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_4_plus_assoc 66
VAL _EVMSC_4_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_11_plus_assoc 67
VAL _EVMSC_11_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVMSC_10_plus_assoc 68
VAL _EVMSC_10_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_9_plus_assoc 69
VAL _EVMSC_9_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_8_plus_assoc 70
VAL _EVMSC_8_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVMSC_7_plus_assoc 71
VAL _EVMSC_7_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_6_plus_assoc 72
VAL _EVMSC_6_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_5_plus_assoc 73
VAL _EVMSC_5_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_3_plus_assoc 74
VAL _EVMSC_3_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_2_plus_assoc 75
VAL _EVMSC_2_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_1_plus_assoc 76
VAL _EVMSC_1_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_plus_assoc 77
VAL _EVMSC_0_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_plus_comm 61
VAL _EVM_plus_comm(VAL v0,VAL v1);
#define FTAG_EVMSC_1_plus_comm 62
VAL _EVMSC_1_plus_comm(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_2_plus_comm 63
VAL _EVMSC_2_plus_comm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_0_plus_comm 64
VAL _EVMSC_0_plus_comm(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_plusnSm 52
VAL _EVM_plusnSm(VAL v0,VAL v1);
#define FTAG_EVMSC_1_plusnSm 53
VAL _EVMSC_1_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_7_plusnSm 54
VAL _EVMSC_7_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_6_plusnSm 55
VAL _EVMSC_6_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_5_plusnSm 56
VAL _EVMSC_5_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_4_plusnSm 57
VAL _EVMSC_4_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6);
#define FTAG_EVMSC_3_plusnSm 58
VAL _EVMSC_3_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_2_plusnSm 59
VAL _EVMSC_2_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_0_plusnSm 60
VAL _EVMSC_0_plusnSm(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_plusnO 49
VAL _EVM_plusnO(VAL v0);
#define FTAG_EVMSC_1_plusnO 50
VAL _EVMSC_1_plusnO(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_plusnO 51
VAL _EVMSC_0_plusnO(VAL v0,VAL v1);
#define FTAG_EVM_discriminate_Nat 47
VAL _EVM_discriminate_Nat(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_discriminate_Nat 48
VAL _EVMSC_0_discriminate_Nat(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_notn_S 44
VAL _EVM_notn_S(VAL v0);
#define FTAG_EVMSC_1_notn_S 45
VAL _EVMSC_1_notn_S(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_notn_S 46
VAL _EVMSC_0_notn_S(VAL v0,VAL v1);
#define FTAG_EVM_notO_S 40
VAL _EVM_notO_S(VAL v0,VAL v1);
#define FTAG_EVMSC_0_notO_S 41
VAL _EVMSC_0_notO_S(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_2_notO_S 42
VAL _EVMSC_2_notO_S(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_1_notO_S 43
VAL _EVMSC_1_notO_S(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVM_s_injective 36
VAL _EVM_s_injective(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_s_injective 37
VAL _EVMSC_0_s_injective(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_2_s_injective 38
VAL _EVMSC_2_s_injective(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_1_s_injective 39
VAL _EVMSC_1_s_injective(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVM_eq_resp_S 34
VAL _EVM_eq_resp_S(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_eq_resp_S 35
VAL _EVMSC_0_eq_resp_S(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_simplifyS 30
VAL _EVM_simplifyS(VAL v0,VAL v1);
#define FTAG_EVMSC_2_simplifyS 31
VAL _EVMSC_2_simplifyS(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_1_simplifyS 32
VAL _EVMSC_1_simplifyS(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_0_simplifyS 33
VAL _EVMSC_0_simplifyS(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_simplifyO 29
VAL _EVM_simplifyO(VAL v0);
#define FTAG_EVM_plus 28
VAL _EVM_plus(VAL v0,VAL v1);
#define FTAG_EVM_pluspr 24
VAL _EVM_pluspr(VAL v0);
#define FTAG_EVMSC_2_pluspr 25
VAL _EVMSC_2_pluspr(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_1_pluspr 26
VAL _EVMSC_1_pluspr(VAL v0,VAL v1);
#define FTAG_EVMSC_0_pluspr 27
VAL _EVMSC_0_pluspr(VAL v0,VAL v1);
#define FTAG_EVM_NatElim 23
VAL _EVM_NatElim(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_or_commutes 19
VAL _EVM_or_commutes(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_2_or_commutes 20
VAL _EVMSC_2_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_1_or_commutes 21
VAL _EVMSC_1_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_or_commutes 22
VAL _EVMSC_0_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_and_commutes 16
VAL _EVM_and_commutes(VAL v0,VAL v1,VAL v2);
#define FTAG_EVMSC_1_and_commutes 17
VAL _EVMSC_1_and_commutes(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVMSC_0_and_commutes 18
VAL _EVMSC_0_and_commutes(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVM_notElim 15
VAL _EVM_notElim(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_not 14
VAL _EVM_not(VAL v0);
#define FTAG_EVM_TrueElim 13
VAL _EVM_TrueElim(VAL v0,VAL v1,VAL v2);
#define FTAG_EVM_FalseElim 12
VAL _EVM_FalseElim(VAL v0,VAL v1);
#define FTAG_EVM_ExElim 11
VAL _EVM_ExElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVM_OrElim 10
VAL _EVM_OrElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVM_AndElim 9
VAL _EVM_AndElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4);
#define FTAG_EVM_eq_resp_f 7
VAL _EVM_eq_resp_f(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_0_eq_resp_f 8
VAL _EVMSC_0_eq_resp_f(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVM_sym 5
VAL _EVM_sym(VAL v0,VAL v1,VAL v2,VAL v3);
#define FTAG_EVMSC_0_sym 6
VAL _EVMSC_0_sym(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVM_trans 3
VAL _EVM_trans(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_0_trans 4
VAL _EVMSC_0_trans(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVM_repl 1
VAL _EVM_repl(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
#define FTAG_EVMSC_0_repl 2
VAL _EVMSC_0_repl(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7);
#define FTAG_EVM_EqElim 0
VAL _EVM_EqElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5);
VAL eval(VAL x) {
    if (x->ty != FUN) return x;
    else {
        function* f = (function*)(x -> info);
        switch(f->ftag) {
            EVALCASE(FTAG_EVM_testval,0,_EVM_testval());
            EVALCASE(FTAG_EVM_testvect2,0,_EVM_testvect2());
            EVALCASE(FTAG_EVM_vectsum,2,_EVM_vectsum(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_vectsum,6,_EVMSC_1_vectsum(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_0_vectsum,4,_EVMSC_0_vectsum(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_testvect,0,_EVM_testvect());
            EVALCASE(FTAG_EVM_vtail,3,_EVM_vtail(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_vtailAux,4,_EVM_vtailAux(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_2_vtailAux,9,_EVMSC_2_vtailAux(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7),FARG(8)));
            EVALCASE(FTAG_EVMSC_3_vtailAux,10,_EVMSC_3_vtailAux(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7),FARG(8),FARG(9)));
            EVALCASE(FTAG_EVMSC_1_vtailAux,5,_EVMSC_1_vtailAux(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_0_vtailAux,6,_EVMSC_0_vtailAux(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVM_FinElim,5,_EVM_FinElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVM_VectElim,6,_EVM_VectElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVM_plus_eq_fst_sym,3,_EVM_plus_eq_fst_sym(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_1_plus_eq_fst_sym,4,_EVMSC_1_plus_eq_fst_sym(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_plus_eq_fst_sym,4,_EVMSC_0_plus_eq_fst_sym(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_plus_eq_fst,3,_EVM_plus_eq_fst(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_2_plus_eq_fst,6,_EVMSC_2_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_8_plus_eq_fst,9,_EVMSC_8_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7),FARG(8)));
            EVALCASE(FTAG_EVMSC_7_plus_eq_fst,7,_EVMSC_7_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_6_plus_eq_fst,7,_EVMSC_6_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_5_plus_eq_fst,9,_EVMSC_5_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7),FARG(8)));
            EVALCASE(FTAG_EVMSC_4_plus_eq_fst,7,_EVMSC_4_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_3_plus_eq_fst,7,_EVMSC_3_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_1_plus_eq_fst,4,_EVMSC_1_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_plus_eq_fst,4,_EVMSC_0_plus_eq_fst(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_plus_assoc,3,_EVM_plus_assoc(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_4_plus_assoc,5,_EVMSC_4_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_11_plus_assoc,8,_EVMSC_11_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVMSC_10_plus_assoc,6,_EVMSC_10_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_9_plus_assoc,6,_EVMSC_9_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_8_plus_assoc,8,_EVMSC_8_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVMSC_7_plus_assoc,6,_EVMSC_7_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_6_plus_assoc,6,_EVMSC_6_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_5_plus_assoc,6,_EVMSC_5_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_3_plus_assoc,6,_EVMSC_3_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_2_plus_assoc,4,_EVMSC_2_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_1_plus_assoc,4,_EVMSC_1_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_plus_assoc,4,_EVMSC_0_plus_assoc(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_plus_comm,2,_EVM_plus_comm(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_plus_comm,4,_EVMSC_1_plus_comm(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_2_plus_comm,5,_EVMSC_2_plus_comm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_0_plus_comm,3,_EVMSC_0_plus_comm(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_plusnSm,2,_EVM_plusnSm(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_1_plusnSm,4,_EVMSC_1_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_7_plusnSm,7,_EVMSC_7_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_6_plusnSm,5,_EVMSC_6_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_5_plusnSm,5,_EVMSC_5_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_4_plusnSm,7,_EVMSC_4_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6)));
            EVALCASE(FTAG_EVMSC_3_plusnSm,5,_EVMSC_3_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_2_plusnSm,5,_EVMSC_2_plusnSm(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_0_plusnSm,3,_EVMSC_0_plusnSm(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_plusnO,1,_EVM_plusnO(FARG(0)));
            EVALCASE(FTAG_EVMSC_1_plusnO,3,_EVMSC_1_plusnO(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_plusnO,2,_EVMSC_0_plusnO(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_discriminate_Nat,3,_EVM_discriminate_Nat(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_discriminate_Nat,4,_EVMSC_0_discriminate_Nat(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_notn_S,1,_EVM_notn_S(FARG(0)));
            EVALCASE(FTAG_EVMSC_1_notn_S,4,_EVMSC_1_notn_S(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_notn_S,2,_EVMSC_0_notn_S(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_notO_S,2,_EVM_notO_S(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_0_notO_S,4,_EVMSC_0_notO_S(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_2_notO_S,6,_EVMSC_2_notO_S(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_1_notO_S,5,_EVMSC_1_notO_S(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVM_s_injective,3,_EVM_s_injective(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_s_injective,4,_EVMSC_0_s_injective(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_2_s_injective,6,_EVMSC_2_s_injective(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_1_s_injective,5,_EVMSC_1_s_injective(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVM_eq_resp_S,3,_EVM_eq_resp_S(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_eq_resp_S,4,_EVMSC_0_eq_resp_S(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_simplifyS,2,_EVM_simplifyS(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_2_simplifyS,5,_EVMSC_2_simplifyS(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_1_simplifyS,3,_EVMSC_1_simplifyS(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_0_simplifyS,3,_EVMSC_0_simplifyS(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_simplifyO,1,_EVM_simplifyO(FARG(0)));
            EVALCASE(FTAG_EVM_plus,2,_EVM_plus(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_pluspr,1,_EVM_pluspr(FARG(0)));
            EVALCASE(FTAG_EVMSC_2_pluspr,4,_EVMSC_2_pluspr(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_1_pluspr,2,_EVMSC_1_pluspr(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVMSC_0_pluspr,2,_EVMSC_0_pluspr(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_NatElim,4,_EVM_NatElim(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_or_commutes,3,_EVM_or_commutes(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_2_or_commutes,4,_EVMSC_2_or_commutes(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_1_or_commutes,4,_EVMSC_1_or_commutes(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_or_commutes,4,_EVMSC_0_or_commutes(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_and_commutes,3,_EVM_and_commutes(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVMSC_1_and_commutes,5,_EVMSC_1_and_commutes(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVMSC_0_and_commutes,4,_EVMSC_0_and_commutes(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVM_notElim,3,_EVM_notElim(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_not,1,_EVM_not(FARG(0)));
            EVALCASE(FTAG_EVM_TrueElim,3,_EVM_TrueElim(FARG(0),FARG(1),FARG(2)));
            EVALCASE(FTAG_EVM_FalseElim,2,_EVM_FalseElim(FARG(0),FARG(1)));
            EVALCASE(FTAG_EVM_ExElim,5,_EVM_ExElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVM_OrElim,6,_EVM_OrElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVM_AndElim,5,_EVM_AndElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4)));
            EVALCASE(FTAG_EVM_eq_resp_f,6,_EVM_eq_resp_f(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_0_eq_resp_f,8,_EVMSC_0_eq_resp_f(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVM_sym,4,_EVM_sym(FARG(0),FARG(1),FARG(2),FARG(3)));
            EVALCASE(FTAG_EVMSC_0_sym,6,_EVMSC_0_sym(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVM_trans,6,_EVM_trans(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_0_trans,8,_EVMSC_0_trans(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVM_repl,6,_EVM_repl(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
            EVALCASE(FTAG_EVMSC_0_repl,8,_EVMSC_0_repl(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5),FARG(6),FARG(7)));
            EVALCASE(FTAG_EVM_EqElim,6,_EVM_EqElim(FARG(0),FARG(1),FARG(2),FARG(3),FARG(4),FARG(5)));
        }
    }
    return x;
}
VAL _EVM_testval() {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp3 = MKCON0(0);
    tmp2 = MKCON1(1,tmp3);
    tmp1 = MKCON1(1,tmp2);
    tmp2 = _EVM_testvect2();
    return _EVM_vectsum(tmp1,tmp2);
}

VAL _EVM_testvect2() {

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
    tmp1 = MKTYPE;
    tmp3 = MKCON0(0);
    tmp2 = MKCON1(1,tmp3);
    tmp4 = MKCON0(0);
    tmp3 = MKCON1(1,tmp4);
    tmp5 = MKTYPE;
    tmp6 = MKCON0(0);
    tmp10 = MKCON0(0);
    tmp9 = MKCON1(1,tmp10);
    tmp8 = MKCON1(1,tmp9);
    tmp7 = MKCON1(1,tmp8);
    tmp9 = MKTYPE;
    tmp8 = MKCON1(0,tmp9);
    args = MKARGS(4);
    args[0] = tmp5;
    args[1] = tmp6;
    args[2] = tmp7;
    args[3] = tmp8;
    tmp4 = MKCONN(1,args,4);
    args = MKARGS(4);
    args[0] = tmp1;
    args[1] = tmp2;
    args[2] = tmp3;
    args[3] = tmp4;
    tmp0 = MKCONN(1,args,4);
    return tmp0;
}

VAL _EVM_vectsum(VAL v0,VAL v1) {

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
    tmp1 = MKTYPE;
    tmp2 = v0;
    tmp3 = v1;
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_0_vectsum,2,tmp5,tmp6);
    tmp5 = MKCON0(0);
    tmp7 = v0;
    tmp8 = v1;
    tmp6 = CLOSURE2(FTAG_EVMSC_1_vectsum,2,tmp7,tmp8);
    return _EVM_VectElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_1_vectsum(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v3;
    tmp2 = v5;
    return _EVM_plus(tmp1,tmp2);
}

VAL _EVMSC_0_vectsum(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_testvect() {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKCON0(0);
    tmp4 = MKCON0(0);
    tmp3 = MKCON1(1,tmp4);
    tmp5 = MKTYPE;
    tmp4 = MKCON1(0,tmp5);
    args = MKARGS(4);
    args[0] = tmp1;
    args[1] = tmp2;
    args[2] = tmp3;
    args[3] = tmp4;
    tmp0 = MKCONN(1,args,4);
    return tmp0;
}

VAL _EVM_vtail(VAL v0,VAL v1,VAL v2) {

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
    tmp2 = v1;
    tmp4 = v1;
    tmp3 = MKCON1(1,tmp4);
    tmp4 = v2;
    tmp6 = MKTYPE;
    tmp8 = v1;
    tmp7 = MKCON1(1,tmp8);
    args = MKARGS(2);
    args[0] = tmp6;
    args[1] = tmp7;
    tmp5 = MKCONN(0,args,2);
    tmp0 = CLOSURE5(FTAG_EVM_vtailAux,5,tmp1,tmp2,tmp3,tmp4,tmp5);
    return tmp0;
}

VAL _EVM_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp4 = CLOSURE4(FTAG_EVMSC_0_vtailAux,4,tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp5 = CLOSURE4(FTAG_EVMSC_1_vtailAux,4,tmp6,tmp7,tmp8,tmp9);
    tmp7 = v0;
    tmp8 = v1;
    tmp9 = v2;
    tmp10 = v3;
    tmp6 = CLOSURE4(FTAG_EVMSC_2_vtailAux,4,tmp7,tmp8,tmp9,tmp10);
    return _EVM_VectElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_2_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8) {

    VAL tmp14;
    VAL tmp13;
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
    tmp1 = MKTYPE;
    tmp2 = v4;
    tmp3 = v1;
    tmp5 = MKTYPE;
    tmp6 = v1;
    tmp7 = v4;
    tmp9 = v1;
    tmp10 = v4;
    tmp11 = v8;
    tmp8 = _EVM_s_injective(tmp9,tmp10,tmp11);
    tmp4 = _EVM_sym(tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    tmp12 = v6;
    tmp13 = v7;
    tmp14 = v8;
    args = MKARGS(9);
    args[0] = tmp6;
    args[1] = tmp7;
    args[2] = tmp8;
    args[3] = tmp9;
    args[4] = tmp10;
    args[5] = tmp11;
    args[6] = tmp12;
    args[7] = tmp13;
    args[8] = tmp14;
    tmp5 = CLOSUREN(FTAG_EVMSC_3_vtailAux,9,args,9);
    tmp6 = v6;
    return _EVM_repl(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_3_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8,VAL v9) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v0;
    tmp3 = v9;
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;
}

VAL _EVMSC_1_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = MKTYPE;
    tmp3 = v0;
    tmp4 = v1;
    tmp1 = CLOSUREADD2(tmp2,tmp3,tmp4);
    tmp2 = v1;
    tmp4 = MKTYPE;
    tmp6 = v1;
    tmp5 = MKCON1(1,tmp6);
    tmp6 = MKCON0(0);
    tmp7 = v4;
    tmp3 = _EVM_sym(tmp4,tmp5,tmp6,tmp7);
    return _EVM_discriminate_Nat(tmp1,tmp2,tmp3);
}

VAL _EVMSC_0_vtailAux(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_FinElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

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
    eval(v1);
    switch(TAG(v1)) {
    case 0:
    tmp1 = v3;
    tmp3 = v1;
    tmp2 = GETCONARG(tmp3,0);
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;

    case 1:
    tmp1 = v4;
    tmp3 = v1;
    tmp2 = GETCONARG(tmp3,0);
    tmp4 = v1;
    tmp3 = GETCONARG(tmp4,1);
    tmp6 = v1;
    tmp5 = GETCONARG(tmp6,0);
    tmp7 = v1;
    tmp6 = GETCONARG(tmp7,1);
    tmp7 = v2;
    tmp8 = v3;
    tmp9 = v4;
    tmp4 = _EVM_FinElim(tmp5,tmp6,tmp7,tmp8,tmp9);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;

    default:
    return NULL;
    }
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

VAL _EVM_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2) {

    VAL tmp16;
    VAL tmp15;
    VAL tmp14;
    VAL tmp13;
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
    tmp1 = MKTYPE;
    tmp3 = v2;
    tmp4 = v0;
    tmp2 = _EVM_plus(tmp3,tmp4);
    tmp4 = v0;
    tmp5 = v2;
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp5 = MKTYPE;
    tmp7 = v0;
    tmp8 = v2;
    tmp6 = _EVM_plus(tmp7,tmp8);
    tmp8 = v2;
    tmp9 = v0;
    tmp7 = _EVM_plus(tmp8,tmp9);
    tmp9 = v0;
    tmp10 = v2;
    tmp8 = _EVM_plus_comm(tmp9,tmp10);
    tmp4 = _EVM_sym(tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp5 = CLOSURE3(FTAG_EVMSC_0_plus_eq_fst_sym,3,tmp6,tmp7,tmp8);
    tmp7 = MKTYPE;
    tmp9 = v2;
    tmp10 = v1;
    tmp8 = _EVM_plus(tmp9,tmp10);
    tmp10 = v1;
    tmp11 = v2;
    tmp9 = _EVM_plus(tmp10,tmp11);
    tmp11 = MKTYPE;
    tmp13 = v1;
    tmp14 = v2;
    tmp12 = _EVM_plus(tmp13,tmp14);
    tmp14 = v2;
    tmp15 = v1;
    tmp13 = _EVM_plus(tmp14,tmp15);
    tmp15 = v1;
    tmp16 = v2;
    tmp14 = _EVM_plus_comm(tmp15,tmp16);
    tmp10 = _EVM_sym(tmp11,tmp12,tmp13,tmp14);
    tmp12 = v0;
    tmp13 = v1;
    tmp14 = v2;
    tmp11 = CLOSURE3(FTAG_EVMSC_1_plus_eq_fst_sym,3,tmp12,tmp13,tmp14);
    tmp13 = v0;
    tmp14 = v1;
    tmp15 = v2;
    tmp12 = _EVM_plus_eq_fst(tmp13,tmp14,tmp15);
    tmp6 = _EVM_repl(tmp7,tmp8,tmp9,tmp10,tmp11,tmp12);
    return _EVM_repl(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_1_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_0_plus_eq_fst_sym(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_plus_eq_fst(VAL v0,VAL v1,VAL v2) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v2;
    tmp3 = v0;
    tmp4 = v1;
    tmp5 = v2;
    tmp2 = CLOSURE3(FTAG_EVMSC_0_plus_eq_fst,3,tmp3,tmp4,tmp5);
    tmp4 = v0;
    tmp5 = v1;
    tmp6 = v2;
    tmp3 = CLOSURE3(FTAG_EVMSC_1_plus_eq_fst,3,tmp4,tmp5,tmp6);
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp4 = CLOSURE3(FTAG_EVMSC_2_plus_eq_fst,3,tmp5,tmp6,tmp7);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_2_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp14;
    VAL tmp13;
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
    tmp1 = v4;
    tmp4 = v3;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    args = MKARGS(6);
    args[0] = tmp6;
    args[1] = tmp7;
    args[2] = tmp8;
    args[3] = tmp9;
    args[4] = tmp10;
    args[5] = tmp11;
    tmp5 = CLOSUREN(FTAG_EVMSC_3_plus_eq_fst,6,args,6);
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
    tmp6 = CLOSUREN(FTAG_EVMSC_4_plus_eq_fst,6,args,6);
    tmp8 = v0;
    tmp9 = v1;
    tmp10 = v2;
    tmp11 = v3;
    tmp12 = v4;
    tmp13 = v5;
    args = MKARGS(6);
    args[0] = tmp8;
    args[1] = tmp9;
    args[2] = tmp10;
    args[3] = tmp11;
    args[4] = tmp12;
    args[5] = tmp13;
    tmp7 = CLOSUREN(FTAG_EVMSC_5_plus_eq_fst,6,args,6);
    tmp8 = v0;
    tmp3 = CLOSURE5(FTAG_EVM_NatElim,5,tmp4,tmp5,tmp6,tmp7,tmp8);
    tmp5 = v3;
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
    tmp6 = CLOSUREN(FTAG_EVMSC_6_plus_eq_fst,6,args,6);
    tmp8 = v0;
    tmp9 = v1;
    tmp10 = v2;
    tmp11 = v3;
    tmp12 = v4;
    tmp13 = v5;
    args = MKARGS(6);
    args[0] = tmp8;
    args[1] = tmp9;
    args[2] = tmp10;
    args[3] = tmp11;
    args[4] = tmp12;
    args[5] = tmp13;
    tmp7 = CLOSUREN(FTAG_EVMSC_7_plus_eq_fst,6,args,6);
    tmp9 = v0;
    tmp10 = v1;
    tmp11 = v2;
    tmp12 = v3;
    tmp13 = v4;
    tmp14 = v5;
    args = MKARGS(6);
    args[0] = tmp9;
    args[1] = tmp10;
    args[2] = tmp11;
    args[3] = tmp12;
    args[4] = tmp13;
    args[5] = tmp14;
    tmp8 = CLOSUREN(FTAG_EVMSC_8_plus_eq_fst,6,args,6);
    tmp9 = v1;
    tmp4 = CLOSURE5(FTAG_EVM_NatElim,5,tmp5,tmp6,tmp7,tmp8,tmp9);
    tmp5 = v5;
    tmp2 = _EVM_s_injective(tmp3,tmp4,tmp5);
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;
}

VAL _EVMSC_8_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v7;
    tmp3 = v8;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_7_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp0;
    VAL* args;
    tmp0 = v6;
    return tmp0;
}

VAL _EVMSC_6_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_5_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7,VAL v8) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v7;
    tmp3 = v8;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_4_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp0;
    VAL* args;
    tmp0 = v6;
    return tmp0;
}

VAL _EVMSC_3_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_1_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = v3;
    return tmp0;
}

VAL _EVMSC_0_plus_eq_fst(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_plus_assoc(VAL v0,VAL v1,VAL v2) {

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
    tmp3 = v0;
    tmp4 = v1;
    tmp5 = v2;
    tmp2 = CLOSURE3(FTAG_EVMSC_0_plus_assoc,3,tmp3,tmp4,tmp5);
    tmp4 = MKTYPE;
    tmp6 = v1;
    tmp8 = v0;
    tmp9 = v1;
    tmp10 = v2;
    tmp7 = CLOSURE3(FTAG_EVMSC_1_plus_assoc,3,tmp8,tmp9,tmp10);
    tmp9 = v0;
    tmp10 = v1;
    tmp11 = v2;
    tmp8 = CLOSURE3(FTAG_EVMSC_2_plus_assoc,3,tmp9,tmp10,tmp11);
    tmp10 = v0;
    tmp11 = v1;
    tmp12 = v2;
    tmp9 = CLOSURE3(FTAG_EVMSC_3_plus_assoc,3,tmp10,tmp11,tmp12);
    tmp10 = v2;
    tmp5 = CLOSURE5(FTAG_EVM_NatElim,5,tmp6,tmp7,tmp8,tmp9,tmp10);
    args = MKARGS(2);
    args[0] = tmp4;
    args[1] = tmp5;
    tmp3 = MKCONN(0,args,2);
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp4 = CLOSURE3(FTAG_EVMSC_4_plus_assoc,3,tmp5,tmp6,tmp7);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_4_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp19;
    VAL tmp18;
    VAL tmp17;
    VAL tmp16;
    VAL tmp15;
    VAL tmp14;
    VAL tmp13;
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
    tmp1 = MKTYPE;
    tmp4 = v3;
    tmp5 = v1;
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp4 = v2;
    tmp2 = _EVM_plus(tmp3,tmp4);
    tmp4 = v3;
    tmp6 = v1;
    tmp7 = v2;
    tmp5 = _EVM_plus(tmp6,tmp7);
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp5 = MKTYPE;
    tmp7 = v3;
    tmp9 = v1;
    tmp10 = v2;
    tmp8 = _EVM_plus(tmp9,tmp10);
    tmp6 = _EVM_plus(tmp7,tmp8);
    tmp9 = v3;
    tmp10 = v1;
    tmp8 = _EVM_plus(tmp9,tmp10);
    tmp9 = v2;
    tmp7 = _EVM_plus(tmp8,tmp9);
    tmp8 = v4;
    tmp4 = _EVM_sym(tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp5 = CLOSURE5(FTAG_EVMSC_5_plus_assoc,5,tmp6,tmp7,tmp8,tmp9,tmp10);
    tmp7 = MKTYPE;
    tmp11 = v3;
    tmp13 = v0;
    tmp14 = v1;
    tmp15 = v2;
    tmp16 = v3;
    tmp17 = v4;
    tmp12 = CLOSURE5(FTAG_EVMSC_6_plus_assoc,5,tmp13,tmp14,tmp15,tmp16,tmp17);
    tmp14 = v0;
    tmp15 = v1;
    tmp16 = v2;
    tmp17 = v3;
    tmp18 = v4;
    tmp13 = CLOSURE5(FTAG_EVMSC_7_plus_assoc,5,tmp14,tmp15,tmp16,tmp17,tmp18);
    tmp15 = v0;
    tmp16 = v1;
    tmp17 = v2;
    tmp18 = v3;
    tmp19 = v4;
    tmp14 = CLOSURE5(FTAG_EVMSC_8_plus_assoc,5,tmp15,tmp16,tmp17,tmp18,tmp19);
    tmp15 = v1;
    tmp10 = CLOSURE5(FTAG_EVM_NatElim,5,tmp11,tmp12,tmp13,tmp14,tmp15);
    tmp12 = v0;
    tmp13 = v1;
    tmp14 = v2;
    tmp15 = v3;
    tmp16 = v4;
    tmp11 = CLOSURE5(FTAG_EVMSC_9_plus_assoc,5,tmp12,tmp13,tmp14,tmp15,tmp16);
    tmp13 = v0;
    tmp14 = v1;
    tmp15 = v2;
    tmp16 = v3;
    tmp17 = v4;
    tmp12 = CLOSURE5(FTAG_EVMSC_10_plus_assoc,5,tmp13,tmp14,tmp15,tmp16,tmp17);
    tmp14 = v0;
    tmp15 = v1;
    tmp16 = v2;
    tmp17 = v3;
    tmp18 = v4;
    tmp13 = CLOSURE5(FTAG_EVMSC_11_plus_assoc,5,tmp14,tmp15,tmp16,tmp17,tmp18);
    tmp14 = v2;
    tmp9 = CLOSURE5(FTAG_EVM_NatElim,5,tmp10,tmp11,tmp12,tmp13,tmp14);
    tmp8 = MKCON1(1,tmp9);
    args = MKARGS(2);
    args[0] = tmp7;
    args[1] = tmp8;
    tmp6 = MKCONN(0,args,2);
    return _EVM_repl(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_11_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v6;
    tmp3 = v7;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_10_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = v5;
    return tmp0;
}

VAL _EVMSC_9_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_8_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v6;
    tmp3 = v7;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_7_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = v5;
    return tmp0;
}

VAL _EVMSC_6_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_5_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

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
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v5;
    tmp3 = MKCON1(1,tmp4);
    tmp7 = v3;
    tmp8 = v1;
    tmp6 = _EVM_plus(tmp7,tmp8);
    tmp5 = MKCON1(1,tmp6);
    tmp6 = v2;
    tmp4 = _EVM_plus(tmp5,tmp6);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVMSC_3_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v4;
    tmp3 = v5;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_2_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = v3;
    return tmp0;
}

VAL _EVMSC_1_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_0_plus_assoc(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v3;
    tmp6 = v1;
    tmp7 = v2;
    tmp5 = _EVM_plus(tmp6,tmp7);
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp6 = v3;
    tmp7 = v1;
    tmp5 = _EVM_plus(tmp6,tmp7);
    tmp6 = v2;
    tmp4 = _EVM_plus(tmp5,tmp6);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_plus_comm(VAL v0,VAL v1) {

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
    tmp3 = v0;
    tmp4 = v1;
    tmp2 = CLOSURE2(FTAG_EVMSC_0_plus_comm,2,tmp3,tmp4);
    tmp4 = MKTYPE;
    tmp6 = v1;
    tmp7 = MKCON0(0);
    tmp5 = _EVM_plus(tmp6,tmp7);
    tmp7 = MKCON0(0);
    tmp8 = v1;
    tmp6 = _EVM_plus(tmp7,tmp8);
    tmp8 = v1;
    tmp7 = _EVM_plusnO(tmp8);
    tmp3 = _EVM_sym(tmp4,tmp5,tmp6,tmp7);
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_1_plus_comm,2,tmp5,tmp6);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_plus_comm(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp1 = MKTYPE;
    tmp3 = v1;
    tmp4 = v2;
    tmp2 = _EVM_plus(tmp3,tmp4);
    tmp4 = v2;
    tmp5 = v1;
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp5 = MKTYPE;
    tmp7 = v2;
    tmp8 = v1;
    tmp6 = _EVM_plus(tmp7,tmp8);
    tmp8 = v1;
    tmp9 = v2;
    tmp7 = _EVM_plus(tmp8,tmp9);
    tmp8 = v3;
    tmp4 = _EVM_sym(tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp5 = CLOSURE4(FTAG_EVMSC_2_plus_comm,4,tmp6,tmp7,tmp8,tmp9);
    tmp7 = MKTYPE;
    tmp9 = v1;
    tmp11 = v2;
    tmp10 = MKCON1(1,tmp11);
    tmp8 = _EVM_plus(tmp9,tmp10);
    tmp11 = v1;
    tmp12 = v2;
    tmp10 = _EVM_plus(tmp11,tmp12);
    tmp9 = MKCON1(1,tmp10);
    tmp11 = v1;
    tmp12 = v2;
    tmp10 = _EVM_plusnSm(tmp11,tmp12);
    tmp6 = _EVM_sym(tmp7,tmp8,tmp9,tmp10);
    return _EVM_repl(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_2_plus_comm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v4;
    tmp3 = MKCON1(1,tmp4);
    tmp5 = v1;
    tmp7 = v2;
    tmp6 = MKCON1(1,tmp7);
    tmp4 = _EVM_plus(tmp5,tmp6);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVMSC_0_plus_comm(VAL v0,VAL v1,VAL v2) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v2;
    tmp5 = v1;
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp5 = v1;
    tmp6 = v2;
    tmp4 = _EVM_plus(tmp5,tmp6);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_plusnSm(VAL v0,VAL v1) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp4 = v1;
    tmp2 = CLOSURE2(FTAG_EVMSC_0_plusnSm,2,tmp3,tmp4);
    tmp4 = MKTYPE;
    tmp6 = v1;
    tmp5 = MKCON1(1,tmp6);
    args = MKARGS(2);
    args[0] = tmp4;
    args[1] = tmp5;
    tmp3 = MKCONN(0,args,2);
    tmp5 = v0;
    tmp6 = v1;
    tmp4 = CLOSURE2(FTAG_EVMSC_1_plusnSm,2,tmp5,tmp6);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp2 = v2;
    tmp4 = v0;
    tmp5 = v1;
    tmp6 = v2;
    tmp7 = v3;
    tmp3 = CLOSURE4(FTAG_EVMSC_2_plusnSm,4,tmp4,tmp5,tmp6,tmp7);
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp8 = v3;
    tmp4 = CLOSURE4(FTAG_EVMSC_3_plusnSm,4,tmp5,tmp6,tmp7,tmp8);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp5 = CLOSURE4(FTAG_EVMSC_4_plusnSm,4,tmp6,tmp7,tmp8,tmp9);
    tmp7 = v1;
    tmp6 = MKCON1(1,tmp7);
    tmp1 = CLOSURE5(FTAG_EVM_NatElim,5,tmp2,tmp3,tmp4,tmp5,tmp6);
    tmp4 = v2;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp5 = CLOSURE4(FTAG_EVMSC_5_plusnSm,4,tmp6,tmp7,tmp8,tmp9);
    tmp7 = v0;
    tmp8 = v1;
    tmp9 = v2;
    tmp10 = v3;
    tmp6 = CLOSURE4(FTAG_EVMSC_6_plusnSm,4,tmp7,tmp8,tmp9,tmp10);
    tmp8 = v0;
    tmp9 = v1;
    tmp10 = v2;
    tmp11 = v3;
    tmp7 = CLOSURE4(FTAG_EVMSC_7_plusnSm,4,tmp8,tmp9,tmp10,tmp11);
    tmp8 = v1;
    tmp3 = CLOSURE5(FTAG_EVM_NatElim,5,tmp4,tmp5,tmp6,tmp7,tmp8);
    tmp2 = MKCON1(1,tmp3);
    tmp3 = v3;
    return _EVM_eq_resp_S(tmp1,tmp2,tmp3);
}

VAL _EVMSC_7_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v5;
    tmp3 = v6;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_6_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = v4;
    return tmp0;
}

VAL _EVMSC_5_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_4_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v5;
    tmp3 = v6;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_3_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = v4;
    return tmp0;
}

VAL _EVMSC_2_plusnSm(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_0_plusnSm(VAL v0,VAL v1,VAL v2) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v2;
    tmp6 = v1;
    tmp5 = MKCON1(1,tmp6);
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp6 = v2;
    tmp7 = v1;
    tmp5 = _EVM_plus(tmp6,tmp7);
    tmp4 = MKCON1(1,tmp5);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_plusnO(VAL v0) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp2 = CLOSURE1(FTAG_EVMSC_0_plusnO,1,tmp3);
    tmp4 = MKTYPE;
    tmp5 = MKCON0(0);
    args = MKARGS(2);
    args[0] = tmp4;
    args[1] = tmp5;
    tmp3 = MKCONN(0,args,2);
    tmp5 = v0;
    tmp4 = CLOSURE1(FTAG_EVMSC_1_plusnO,1,tmp5);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_plusnO(VAL v0,VAL v1,VAL v2) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v1;
    tmp3 = MKCON0(0);
    tmp1 = _EVM_plus(tmp2,tmp3);
    tmp2 = v1;
    tmp3 = v2;
    return _EVM_eq_resp_S(tmp1,tmp2,tmp3);
}

VAL _EVMSC_0_plusnO(VAL v0,VAL v1) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v1;
    tmp5 = MKCON0(0);
    tmp3 = _EVM_plus(tmp4,tmp5);
    tmp4 = v1;
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_discriminate_Nat(VAL v0,VAL v1,VAL v2) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v1;
    tmp3 = v2;
    tmp1 = _EVM_notO_S(tmp2,tmp3);
    tmp3 = v0;
    tmp4 = v1;
    tmp5 = v2;
    tmp2 = CLOSURE3(FTAG_EVMSC_0_discriminate_Nat,3,tmp3,tmp4,tmp5);
    return _EVM_FalseElim(tmp1,tmp2);
}

VAL _EVMSC_0_discriminate_Nat(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp0;
    VAL* args;
    tmp0 = v0;
    return tmp0;
}

VAL _EVM_notn_S(VAL v0) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp2 = CLOSURE1(FTAG_EVMSC_0_notn_S,1,tmp3);
    tmp4 = MKCON0(0);
    tmp3 = CLOSURE1(FTAG_EVM_notO_S,1,tmp4);
    tmp5 = v0;
    tmp4 = CLOSURE1(FTAG_EVMSC_1_notn_S,1,tmp5);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_1_notn_S(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v2;
    tmp3 = v1;
    tmp5 = v1;
    tmp4 = MKCON1(1,tmp5);
    tmp5 = v3;
    tmp2 = _EVM_s_injective(tmp3,tmp4,tmp5);
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;
}

VAL _EVMSC_0_notn_S(VAL v0,VAL v1) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = MKTYPE;
    tmp3 = MKTYPE;
    tmp4 = v1;
    tmp6 = v1;
    tmp5 = MKCON1(1,tmp6);
    tmp1 = CLOSUREADD3(tmp2,tmp3,tmp4,tmp5);
    return _EVM_not(tmp1);
}

VAL _EVM_notO_S(VAL v0,VAL v1) {

    VAL tmp7;
    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKCON0(0);
    tmp4 = v0;
    tmp3 = MKCON1(1,tmp4);
    tmp4 = v1;
    tmp6 = v0;
    tmp7 = v1;
    tmp5 = CLOSURE2(FTAG_EVMSC_0_notO_S,2,tmp6,tmp7);
    tmp6 = MKCON0(0);
    return _EVM_EqElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_notO_S(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp1 = v2;
    tmp3 = v0;
    tmp4 = v1;
    tmp5 = v2;
    tmp6 = v3;
    tmp2 = CLOSURE4(FTAG_EVMSC_1_notO_S,4,tmp3,tmp4,tmp5,tmp6);
    tmp3 = MKTYPE;
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp8 = v3;
    tmp4 = CLOSURE4(FTAG_EVMSC_2_notO_S,4,tmp5,tmp6,tmp7,tmp8);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_2_notO_S(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVMSC_1_notO_S(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_s_injective(VAL v0,VAL v1,VAL v2) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v0;
    tmp5 = v1;
    tmp6 = v2;
    tmp3 = CLOSURE3(FTAG_EVMSC_0_s_injective,3,tmp4,tmp5,tmp6);
    tmp5 = v0;
    tmp4 = MKCON1(1,tmp5);
    tmp6 = v1;
    tmp5 = MKCON1(1,tmp6);
    tmp6 = v2;
    return _EVM_eq_resp_f(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_s_injective(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp1 = v3;
    tmp3 = v0;
    tmp4 = v1;
    tmp5 = v2;
    tmp6 = v3;
    tmp2 = CLOSURE4(FTAG_EVMSC_1_s_injective,4,tmp3,tmp4,tmp5,tmp6);
    tmp3 = v0;
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp8 = v3;
    tmp4 = CLOSURE4(FTAG_EVMSC_2_s_injective,4,tmp5,tmp6,tmp7,tmp8);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_2_s_injective(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    tmp0 = v4;
    return tmp0;
}

VAL _EVMSC_1_s_injective(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_eq_resp_S(VAL v0,VAL v1,VAL v2) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = MKTYPE;
    tmp4 = v0;
    tmp5 = v1;
    tmp6 = v2;
    tmp3 = CLOSURE3(FTAG_EVMSC_0_eq_resp_S,3,tmp4,tmp5,tmp6);
    tmp4 = v0;
    tmp5 = v1;
    tmp6 = v2;
    return _EVM_eq_resp_f(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_eq_resp_S(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v3;
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVM_simplifyS(VAL v0,VAL v1) {

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
    tmp1 = MKTYPE;
    tmp4 = v0;
    tmp6 = v0;
    tmp7 = v1;
    tmp5 = CLOSURE2(FTAG_EVMSC_0_simplifyS,2,tmp6,tmp7);
    tmp7 = v0;
    tmp8 = v1;
    tmp6 = CLOSURE2(FTAG_EVMSC_1_simplifyS,2,tmp7,tmp8);
    tmp8 = v0;
    tmp9 = v1;
    tmp7 = CLOSURE2(FTAG_EVMSC_2_simplifyS,2,tmp8,tmp9);
    tmp8 = v1;
    tmp3 = CLOSURE5(FTAG_EVM_NatElim,5,tmp4,tmp5,tmp6,tmp7,tmp8);
    tmp2 = MKCON1(1,tmp3);
    args = MKARGS(2);
    args[0] = tmp1;
    args[1] = tmp2;
    tmp0 = MKCONN(0,args,2);
    return tmp0;
}

VAL _EVMSC_2_simplifyS(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp2 = v3;
    tmp3 = v4;
    tmp1 = CLOSUREADD1(tmp2,tmp3);
    tmp0 = MKCON1(1,tmp1);
    return tmp0;
}

VAL _EVMSC_1_simplifyS(VAL v0,VAL v1,VAL v2) {

    VAL tmp0;
    VAL* args;
    tmp0 = v2;
    return tmp0;
}

VAL _EVMSC_0_simplifyS(VAL v0,VAL v1,VAL v2) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_simplifyO(VAL v0) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v0;
    args = MKARGS(2);
    args[0] = tmp1;
    args[1] = tmp2;
    tmp0 = MKCONN(0,args,2);
    return tmp0;
}

VAL _EVM_plus(VAL v0,VAL v1) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp2 = v1;
    tmp0 = CLOSURE2(FTAG_EVM_pluspr,2,tmp1,tmp2);
    return tmp0;
}

VAL _EVM_pluspr(VAL v0) {

    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v0;
    tmp3 = v0;
    tmp2 = CLOSURE1(FTAG_EVMSC_0_pluspr,1,tmp3);
    tmp4 = v0;
    tmp3 = CLOSURE1(FTAG_EVMSC_1_pluspr,1,tmp4);
    tmp5 = v0;
    tmp4 = CLOSURE1(FTAG_EVMSC_2_pluspr,1,tmp5);
    return _EVM_NatElim(tmp1,tmp2,tmp3,tmp4);
}

VAL _EVMSC_2_pluspr(VAL v0,VAL v1,VAL v2,VAL v3) {

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

VAL _EVMSC_1_pluspr(VAL v0,VAL v1) {

    VAL tmp0;
    VAL* args;
    tmp0 = v1;
    return tmp0;
}

VAL _EVMSC_0_pluspr(VAL v0,VAL v1) {

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

VAL _EVM_or_commutes(VAL v0,VAL v1,VAL v2) {

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
    tmp2 = v1;
    tmp3 = v2;
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp4 = CLOSURE3(FTAG_EVMSC_0_or_commutes,3,tmp5,tmp6,tmp7);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp5 = CLOSURE3(FTAG_EVMSC_1_or_commutes,3,tmp6,tmp7,tmp8);
    tmp7 = v0;
    tmp8 = v1;
    tmp9 = v2;
    tmp6 = CLOSURE3(FTAG_EVMSC_2_or_commutes,3,tmp7,tmp8,tmp9);
    return _EVM_OrElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_2_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp2 = v0;
    tmp3 = v3;
    args = MKARGS(3);
    args[0] = tmp1;
    args[1] = tmp2;
    args[2] = tmp3;
    tmp0 = MKCONN(0,args,3);
    return tmp0;
}

VAL _EVMSC_1_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp2 = v0;
    tmp3 = v3;
    args = MKARGS(3);
    args[0] = tmp1;
    args[1] = tmp2;
    args[2] = tmp3;
    tmp0 = MKCONN(1,args,3);
    return tmp0;
}

VAL _EVMSC_0_or_commutes(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v1;
    tmp3 = v0;
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;
}

VAL _EVM_and_commutes(VAL v0,VAL v1,VAL v2) {

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
    tmp2 = v1;
    tmp3 = v2;
    tmp5 = v0;
    tmp6 = v1;
    tmp7 = v2;
    tmp4 = CLOSURE3(FTAG_EVMSC_0_and_commutes,3,tmp5,tmp6,tmp7);
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp5 = CLOSURE3(FTAG_EVMSC_1_and_commutes,3,tmp6,tmp7,tmp8);
    return _EVM_AndElim(tmp1,tmp2,tmp3,tmp4,tmp5);
}

VAL _EVMSC_1_and_commutes(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp2 = v0;
    tmp3 = v4;
    tmp4 = v3;
    args = MKARGS(4);
    args[0] = tmp1;
    args[1] = tmp2;
    args[2] = tmp3;
    args[3] = tmp4;
    tmp0 = MKCONN(0,args,4);
    return tmp0;
}

VAL _EVMSC_0_and_commutes(VAL v0,VAL v1,VAL v2,VAL v3) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v1;
    tmp3 = v0;
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;
}

VAL _EVM_notElim(VAL v0,VAL v1,VAL v2) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v1;
    tmp2 = v2;
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;
}

VAL _EVM_not(VAL v0) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_TrueElim(VAL v0,VAL v1,VAL v2) {

    VAL tmp0;
    VAL* args;
    eval(v0);
    switch(TAG(v0)) {
    case 0:
    tmp0 = v2;
    return tmp0;

    default:
    return NULL;
    }
}

VAL _EVM_FalseElim(VAL v0,VAL v1) {

    VAL tmp0;
    VAL* args;
    tmp0 = MKTYPE;
    return tmp0;
}

VAL _EVM_ExElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    eval(v2);
    switch(TAG(v2)) {
    case 0:
    tmp1 = v4;
    tmp3 = v2;
    tmp2 = GETCONARG(tmp3,2);
    tmp4 = v2;
    tmp3 = GETCONARG(tmp4,3);
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;

    default:
    return NULL;
    }
}

VAL _EVM_OrElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    eval(v2);
    switch(TAG(v2)) {
    case 0:
    tmp1 = v4;
    tmp3 = v2;
    tmp2 = GETCONARG(tmp3,2);
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;

    case 1:
    tmp1 = v5;
    tmp3 = v2;
    tmp2 = GETCONARG(tmp3,2);
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;

    default:
    return NULL;
    }
}

VAL _EVM_AndElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4) {

    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    eval(v2);
    switch(TAG(v2)) {
    case 0:
    tmp1 = v4;
    tmp3 = v2;
    tmp2 = GETCONARG(tmp3,2);
    tmp4 = v2;
    tmp3 = GETCONARG(tmp4,3);
    tmp0 = CLOSUREADD2(tmp1,tmp2,tmp3);
    return tmp0;

    default:
    return NULL;
    }
}

VAL _EVM_eq_resp_f(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

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
    tmp2 = v3;
    tmp3 = v4;
    tmp4 = v5;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    args = MKARGS(6);
    args[0] = tmp6;
    args[1] = tmp7;
    args[2] = tmp8;
    args[3] = tmp9;
    args[4] = tmp10;
    args[5] = tmp11;
    tmp5 = CLOSUREN(FTAG_EVMSC_0_eq_resp_f,6,args,6);
    tmp7 = v1;
    tmp9 = v2;
    tmp10 = v3;
    tmp8 = CLOSUREADD1(tmp9,tmp10);
    args = MKARGS(2);
    args[0] = tmp7;
    args[1] = tmp8;
    tmp6 = MKCONN(0,args,2);
    return _EVM_EqElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_eq_resp_f(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp6;
    VAL tmp5;
    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v1;
    tmp4 = v2;
    tmp5 = v3;
    tmp3 = CLOSUREADD1(tmp4,tmp5);
    tmp5 = v2;
    tmp6 = v6;
    tmp4 = CLOSUREADD1(tmp5,tmp6);
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_sym(VAL v0,VAL v1,VAL v2,VAL v3) {

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
    tmp2 = v1;
    tmp3 = v2;
    tmp4 = v3;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp5 = CLOSURE4(FTAG_EVMSC_0_sym,4,tmp6,tmp7,tmp8,tmp9);
    tmp7 = v0;
    tmp8 = v1;
    args = MKARGS(2);
    args[0] = tmp7;
    args[1] = tmp8;
    tmp6 = MKCONN(0,args,2);
    return _EVM_EqElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_sym(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v0;
    tmp3 = v4;
    tmp4 = v1;
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_trans(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

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
    tmp4 = v5;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    args = MKARGS(6);
    args[0] = tmp6;
    args[1] = tmp7;
    args[2] = tmp8;
    args[3] = tmp9;
    args[4] = tmp10;
    args[5] = tmp11;
    tmp5 = CLOSUREN(FTAG_EVMSC_0_trans,6,args,6);
    tmp6 = v4;
    return _EVM_EqElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_trans(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp4;
    VAL tmp3;
    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = MKTYPE;
    tmp2 = v0;
    tmp3 = v1;
    tmp4 = v6;
    tmp0 = CLOSUREADD3(tmp1,tmp2,tmp3,tmp4);
    return tmp0;
}

VAL _EVM_repl(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

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
    tmp2 = v1;
    tmp3 = v2;
    tmp4 = v3;
    tmp6 = v0;
    tmp7 = v1;
    tmp8 = v2;
    tmp9 = v3;
    tmp10 = v4;
    tmp11 = v5;
    args = MKARGS(6);
    args[0] = tmp6;
    args[1] = tmp7;
    args[2] = tmp8;
    args[3] = tmp9;
    args[4] = tmp10;
    args[5] = tmp11;
    tmp5 = CLOSUREN(FTAG_EVMSC_0_repl,6,args,6);
    tmp6 = v5;
    return _EVM_EqElim(tmp1,tmp2,tmp3,tmp4,tmp5,tmp6);
}

VAL _EVMSC_0_repl(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5,VAL v6,VAL v7) {

    VAL tmp2;
    VAL tmp1;
    VAL tmp0;
    VAL* args;
    tmp1 = v4;
    tmp2 = v6;
    tmp0 = CLOSUREADD1(tmp1,tmp2);
    return tmp0;
}

VAL _EVM_EqElim(VAL v0,VAL v1,VAL v2,VAL v3,VAL v4,VAL v5) {

    VAL tmp0;
    VAL* args;
    eval(v3);
    switch(TAG(v3)) {
    case 0:
    tmp0 = v5;
    return tmp0;

    default:
    return NULL;
    }
}

