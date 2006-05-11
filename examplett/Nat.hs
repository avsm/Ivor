{-# OPTIONS_GHC -fglasgow-exts #-} 

module Nat where

import GHC.Base

coerce :: a -> b
coerce = unsafeCoerce#

data Type = Type
data Val = Val

class Project x where
    project :: forall val. Int -> x -> val

data TT_Nat = TT_O | forall arg. TT_S arg 

instance Project TT_Nat where
    project 0 (TT_S  a0) = ((coerce a0)::val)



fn_NatElim :: val -> val -> val -> val -> val
fn_NatElim = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (case ((coerce v0)::TT_Nat) of { TT_O  -> v2 ; TT_S _  -> (((coerce v3)::val->val->val) ((coerce (project 0((coerce v0)::TT_Nat)))::val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val) ((coerce (project 0((coerce v0)::TT_Nat)))::val) ((coerce v1)::val) ((coerce v2)::val) ((coerce v3)::val) ))::val) ) ; })))))

data TT_True = TT_II 
fn_TrueElim :: val -> val -> val -> val
fn_TrueElim = (\v0 -> (\v1 -> (\v2 -> (case ((coerce v0)::TT_True) of { TT_II  -> v2 ; }))))

data TT_False = TT_False
fn_FalseElim :: val -> val -> val
fn_FalseElim = (\v0 -> (\v1 -> error "Impossible"))

data TT_Ex = forall arg. TT_ex_intro arg arg arg arg 

instance Project TT_Ex where
    project 3 (TT_ex_intro  a0 a1 a2 a3) = ((coerce a3)::val)
    project 2 (TT_ex_intro  a0 a1 a2 a3) = ((coerce a2)::val)
    project 1 (TT_ex_intro  a0 a1 a2 a3) = ((coerce a1)::val)
    project 0 (TT_ex_intro  a0 a1 a2 a3) = ((coerce a0)::val)



fn_ExElim :: val -> val -> val -> val -> val -> val
fn_ExElim = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (case ((coerce v2)::TT_Ex) of { TT_ex_intro _ _ _ _  -> (((coerce v4)::val->val->val) ((coerce (project 2((coerce v2)::TT_Ex)))::val) ((coerce (project 3((coerce v2)::TT_Ex)))::val) ) ; }))))))

data TT_Or = forall arg. TT_or_intro_l arg arg arg | forall arg. TT_or_intro_r arg arg arg 

instance Project TT_Or where
    project 2 (TT_or_intro_l  a0 a1 a2) = ((coerce a2)::val)
    project 1 (TT_or_intro_l  a0 a1 a2) = ((coerce a1)::val)
    project 0 (TT_or_intro_l  a0 a1 a2) = ((coerce a0)::val)


    project 2 (TT_or_intro_r  a0 a1 a2) = ((coerce a2)::val)
    project 1 (TT_or_intro_r  a0 a1 a2) = ((coerce a1)::val)
    project 0 (TT_or_intro_r  a0 a1 a2) = ((coerce a0)::val)



fn_OrElim :: val -> val -> val -> val -> val -> val -> val
fn_OrElim = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (\v5 -> (case ((coerce v2)::TT_Or) of { TT_or_intro_l _ _ _  -> (((coerce v4)::val->val) ((coerce (project 2((coerce v2)::TT_Or)))::val) ) ; TT_or_intro_r _ _ _  -> (((coerce v5)::val->val) ((coerce (project 2((coerce v2)::TT_Or)))::val) ) ; })))))))

data TT_And = forall arg. TT_and_intro arg arg arg arg 

instance Project TT_And where
    project 3 (TT_and_intro  a0 a1 a2 a3) = ((coerce a3)::val)
    project 2 (TT_and_intro  a0 a1 a2 a3) = ((coerce a2)::val)
    project 1 (TT_and_intro  a0 a1 a2 a3) = ((coerce a1)::val)
    project 0 (TT_and_intro  a0 a1 a2 a3) = ((coerce a0)::val)



fn_AndElim :: val -> val -> val -> val -> val -> val
fn_AndElim = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (case ((coerce v2)::TT_And) of { TT_and_intro _ _ _ _  -> (((coerce v4)::val->val->val) ((coerce (project 2((coerce v2)::TT_And)))::val) ((coerce (project 3((coerce v2)::TT_And)))::val) ) ; }))))))

data TT_Eq = forall arg. TT_refl arg arg 

instance Project TT_Eq where
    project 1 (TT_refl  a0 a1) = ((coerce a1)::val)
    project 0 (TT_refl  a0 a1) = ((coerce a0)::val)



fn_EqElim :: val -> val -> val -> val -> val -> val -> val
fn_EqElim = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (\v5 -> (case ((coerce v3)::TT_Eq) of { TT_refl _ _  -> v5 ; })))))))

fn_plus_eq_fst_sym :: val -> val -> val -> val -> val
fn_plus_eq_fst_sym = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_repl)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v0)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v0)::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v0)::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v0)::val) ))::val) ((coerce (((coerce fn_plus_comm)::val->val->val) ((coerce v0)::val) ((coerce v2)::val) ))::val) ))::val) ((coerce (\v3 -> ((coerce Type)::val)))::val) ((coerce (((coerce fn_repl)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_plus_comm)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ((coerce (\v3 -> ((coerce Type)::val)))::val) ((coerce (((coerce fn_plus_eq_fst)::val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ))))

fn_plus_eq_fst :: val -> val -> val -> val -> val
fn_plus_eq_fst = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v2)::val) ((coerce (\v3 -> ((coerce Type)::val)))::val) ((coerce (\v3 -> v3))::val) ((coerce (\v3 -> (\v4 -> (\v5 -> (((coerce v4)::val->val) ((coerce (((coerce fn_s_injective)::val->val->val->val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v3)::val) ((coerce (\v6 -> ((coerce Type)::val)))::val) ((coerce (\v6 -> v6))::val) ((coerce (\v6 -> (\v7 -> (\v8 -> (coerce (TT_S ((coerce (((coerce v7)::val->val) ((coerce v8)::val) ))::val) )::val)))))::val) ((coerce v0)::val) ))::val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v3)::val) ((coerce (\v6 -> ((coerce Type)::val)))::val) ((coerce (\v6 -> v6))::val) ((coerce (\v6 -> (\v7 -> (\v8 -> (coerce (TT_S ((coerce (((coerce v7)::val->val) ((coerce v8)::val) ))::val) )::val)))))::val) ((coerce v1)::val) ))::val) ((coerce v5)::val) ))::val) )))))::val) ))))

fn_plus_assoc :: val -> val -> val -> val
fn_plus_assoc = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v3 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce v1)::val) ))::val) ((coerce v2)::val) ))::val) )))::val) ((coerce (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v1)::val) ((coerce (\v3 -> ((coerce Type)::val)))::val) ((coerce (\v3 -> v3))::val) ((coerce (\v3 -> (\v4 -> (\v5 -> (coerce (TT_S ((coerce (((coerce v4)::val->val) ((coerce v5)::val) ))::val) )::val)))))::val) ((coerce v2)::val) ))::val) )::val))::val) ((coerce (\v3 -> (\v4 -> (((coerce fn_repl)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce v1)::val) ))::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce v1)::val) ))::val) ((coerce v2)::val) ))::val) ((coerce v4)::val) ))::val) ((coerce (\v5 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_S ((coerce v5)::val) )::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce (coerce (TT_S ((coerce (((coerce fn_plus)::val->val->val) ((coerce v3)::val) ((coerce v1)::val) ))::val) )::val))::val) ((coerce v2)::val) ))::val) )))::val) ((coerce (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_S ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v3)::val) ((coerce (\v5 -> ((coerce Type)::val)))::val) ((coerce (\v5 -> v5))::val) ((coerce (\v5 -> (\v6 -> (\v7 -> (coerce (TT_S ((coerce (((coerce v6)::val->val) ((coerce v7)::val) ))::val) )::val)))))::val) ((coerce v1)::val) ))::val) ((coerce (\v5 -> ((coerce Type)::val)))::val) ((coerce (\v5 -> v5))::val) ((coerce (\v5 -> (\v6 -> (\v7 -> (coerce (TT_S ((coerce (((coerce v6)::val->val) ((coerce v7)::val) ))::val) )::val)))))::val) ((coerce v2)::val) ))::val) )::val))::val) )::val))::val) ))))::val) ))))

fn_plus_comm :: val -> val -> val
fn_plus_comm = (\v0 -> (\v1 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v2 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) )))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_O )::val))::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce (coerce (TT_O )::val))::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_plusnO)::val->val) ((coerce v1)::val) ))::val) ))::val) ((coerce (\v2 -> (\v3 -> (((coerce fn_repl)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ((coerce v3)::val) ))::val) ((coerce (\v4 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_S ((coerce v4)::val) )::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_S ((coerce v2)::val) )::val))::val) ))::val) )))::val) ((coerce (((coerce fn_sym)::val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_S ((coerce v2)::val) )::val))::val) ))::val) ((coerce (coerce (TT_S ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) )::val))::val) ((coerce (((coerce fn_plusnSm)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ))::val) ))))::val) )))

fn_plusnSm :: val -> val -> val
fn_plusnSm = (\v0 -> (\v1 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v2 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) ))::val) ((coerce (coerce (TT_S ((coerce (((coerce fn_plus)::val->val->val) ((coerce v2)::val) ((coerce v1)::val) ))::val) )::val))::val) )))::val) ((coerce (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) )::val))::val) ((coerce (\v2 -> (\v3 -> (((coerce fn_eq_resp_S)::val->val->val->val) ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v2)::val) ((coerce (\v4 -> ((coerce Type)::val)))::val) ((coerce (\v4 -> v4))::val) ((coerce (\v4 -> (\v5 -> (\v6 -> (coerce (TT_S ((coerce (((coerce v5)::val->val) ((coerce v6)::val) ))::val) )::val)))))::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) ))::val) ((coerce (coerce (TT_S ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v2)::val) ((coerce (\v4 -> ((coerce Type)::val)))::val) ((coerce (\v4 -> v4))::val) ((coerce (\v4 -> (\v5 -> (\v6 -> (coerce (TT_S ((coerce (((coerce v5)::val->val) ((coerce v6)::val) ))::val) )::val)))))::val) ((coerce v1)::val) ))::val) )::val))::val) ((coerce v3)::val) ))))::val) )))

fn_plusnO :: val -> val
fn_plusnO = (\v0 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v1 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_O )::val))::val) ))::val) ((coerce v1)::val) )))::val) ((coerce (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_O )::val))::val) )::val))::val) ((coerce (\v1 -> (\v2 -> (((coerce fn_eq_resp_S)::val->val->val->val) ((coerce (((coerce fn_plus)::val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_O )::val))::val) ))::val) ((coerce v1)::val) ((coerce v2)::val) ))))::val) ))

fn_discriminate_Nat :: val -> val -> val -> val
fn_discriminate_Nat = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_FalseElim)::val->val->val) ((coerce (((coerce fn_notO_S)::val->val->val) ((coerce v1)::val) ((coerce v2)::val) ))::val) ((coerce (\v3 -> v0))::val) ))))

fn_notn_S :: val -> val -> val
fn_notn_S = (\v0 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v1 -> (((coerce fn_not)::val->val) ((coerce (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce v1)::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) ))::val) )))::val) ((coerce (((coerce fn_notO_S)::val->val) ((coerce (coerce (TT_O )::val))::val) ))::val) ((coerce (\v1 -> (\v2 -> (\v3 -> (((coerce v2)::val->val) ((coerce (((coerce fn_s_injective)::val->val->val->val) ((coerce v1)::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) ((coerce v3)::val) ))::val) )))))::val) ))

fn_notO_S :: val -> val -> val
fn_notO_S = (\v0 -> (\v1 -> (((coerce fn_EqElim)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_O )::val))::val) ((coerce (coerce (TT_S ((coerce v0)::val) )::val))::val) ((coerce v1)::val) ((coerce (\v2 -> (\v3 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v2)::val) ((coerce (\v4 -> ((coerce Type)::val)))::val) ((coerce ((coerce Type)::val))::val) ((coerce (\v4 -> (\v5 -> ((coerce Type)::val))))::val) ))))::val) ((coerce (coerce (TT_II )::val))::val) )))

fn_s_injective :: val -> val -> val -> val
fn_s_injective = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_eq_resp_f)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce ((coerce Type)::val))::val) ((coerce (\v3 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v3)::val) ((coerce (\v4 -> ((coerce Type)::val)))::val) ((coerce v0)::val) ((coerce (\v4 -> (\v5 -> v4)))::val) )))::val) ((coerce (coerce (TT_S ((coerce v0)::val) )::val))::val) ((coerce (coerce (TT_S ((coerce v1)::val) )::val))::val) ((coerce v2)::val) ))))

fn_eq_resp_S :: val -> val -> val -> val
fn_eq_resp_S = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_eq_resp_f)::val->val->val->val->val->val->val) ((coerce ((coerce Type)::val))::val) ((coerce ((coerce Type)::val))::val) ((coerce (\v3 -> (coerce (TT_S ((coerce v3)::val) )::val)))::val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ))))

fn_simplifyS :: val -> val -> val
fn_simplifyS = (\v0 -> (\v1 -> (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce (coerce (TT_S ((coerce (((coerce fn_NatElim)::val->val->val->val->val->val) ((coerce v0)::val) ((coerce (\v2 -> ((coerce Type)::val)))::val) ((coerce (\v2 -> v2))::val) ((coerce (\v2 -> (\v3 -> (\v4 -> (coerce (TT_S ((coerce (((coerce v3)::val->val) ((coerce v4)::val) ))::val) )::val)))))::val) ((coerce v1)::val) ))::val) )::val))::val) )::val)))

fn_simplifyO :: val -> val
fn_simplifyO = (\v0 -> (coerce (TT_refl ((coerce ((coerce Type)::val))::val) ((coerce v0)::val) )::val))

fn_plus :: val -> val -> val
fn_plus = (\v0 -> (\v1 -> (((coerce fn_plus_AP_)::val->val->val) ((coerce v0)::val) ((coerce v1)::val) )))

fn_plus_AP_ :: val -> val -> val
fn_plus_AP_ = (\v0 -> (((coerce fn_NatElim)::val->val->val->val->val) ((coerce v0)::val) ((coerce (\v1 -> ((coerce Type)::val)))::val) ((coerce (\v1 -> v1))::val) ((coerce (\v1 -> (\v2 -> (\v3 -> (coerce (TT_S ((coerce (((coerce v2)::val->val) ((coerce v3)::val) ))::val) )::val)))))::val) ))

fn_or_commutes :: val -> val -> val -> val
fn_or_commutes = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_OrElim)::val->val->val->val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ((coerce (\v3 -> (((coerce ((coerce Type)::val))::val->val->val) ((coerce v1)::val) ((coerce v0)::val) )))::val) ((coerce (\v3 -> (coerce (TT_or_intro_r ((coerce v1)::val) ((coerce v0)::val) ((coerce v3)::val) )::val)))::val) ((coerce (\v3 -> (coerce (TT_or_intro_l ((coerce v1)::val) ((coerce v0)::val) ((coerce v3)::val) )::val)))::val) ))))

fn_and_commutes :: val -> val -> val -> val
fn_and_commutes = (\v0 -> (\v1 -> (\v2 -> (((coerce fn_AndElim)::val->val->val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ((coerce (\v3 -> (((coerce ((coerce Type)::val))::val->val->val) ((coerce v1)::val) ((coerce v0)::val) )))::val) ((coerce (\v3 -> (\v4 -> (coerce (TT_and_intro ((coerce v1)::val) ((coerce v0)::val) ((coerce v4)::val) ((coerce v3)::val) )::val))))::val) ))))

fn_notElim :: val -> val -> val -> val
fn_notElim = (\v0 -> (\v1 -> (\v2 -> (((coerce v1)::val->val) ((coerce v2)::val) ))))

fn_not :: val -> val
fn_not = (\v0 -> ((coerce Type)::val))

fn_eq_resp_f :: val -> val -> val -> val -> val -> val -> val
fn_eq_resp_f = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (\v5 -> (((coerce fn_EqElim)::val->val->val->val->val->val->val) ((coerce v0)::val) ((coerce v3)::val) ((coerce v4)::val) ((coerce v5)::val) ((coerce (\v6 -> (\v7 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce v1)::val) ((coerce (((coerce v2)::val->val) ((coerce v3)::val) ))::val) ((coerce (((coerce v2)::val->val) ((coerce v6)::val) ))::val) ))))::val) ((coerce (coerce (TT_refl ((coerce v1)::val) ((coerce (((coerce v2)::val->val) ((coerce v3)::val) ))::val) )::val))::val) )))))))

fn_sym :: val -> val -> val -> val -> val
fn_sym = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (((coerce fn_EqElim)::val->val->val->val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ((coerce v3)::val) ((coerce (\v4 -> (\v5 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce v0)::val) ((coerce v4)::val) ((coerce v1)::val) ))))::val) ((coerce (coerce (TT_refl ((coerce v0)::val) ((coerce v1)::val) )::val))::val) )))))

fn_trans :: val -> val -> val -> val -> val -> val -> val
fn_trans = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (\v5 -> (((coerce fn_EqElim)::val->val->val->val->val->val->val) ((coerce v0)::val) ((coerce v2)::val) ((coerce v3)::val) ((coerce v5)::val) ((coerce (\v6 -> (\v7 -> (((coerce ((coerce Type)::val))::val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v6)::val) ))))::val) ((coerce v4)::val) )))))))

fn_repl :: val -> val -> val -> val -> val -> val -> val
fn_repl = (\v0 -> (\v1 -> (\v2 -> (\v3 -> (\v4 -> (\v5 -> (((coerce fn_EqElim)::val->val->val->val->val->val->val) ((coerce v0)::val) ((coerce v1)::val) ((coerce v2)::val) ((coerce v3)::val) ((coerce (\v6 -> (\v7 -> (((coerce v4)::val->val) ((coerce v6)::val) ))))::val) ((coerce v5)::val) )))))))

