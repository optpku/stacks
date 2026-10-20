/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.BaseChange.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.90.15 (05EQ)

@stack 05EQ
-/

-- Lemma 15.90.15, the middle vertical functor in the formal-gluing base-change diagram.
@[stacks 05EQ "Lemma 15.90.15, formal-gluing base-change functor"]
#check @LocalizedModule.Away.FormalGluing.tensorBaseChangeFunctor

-- Lemma 15.90.15, commutativity of the square containing `Can`.
@[stacks 05EQ "Lemma 15.90.15, Can square"]
#check @LocalizedModule.Away.FormalGluing.canTensorBaseChangeIso

-- Lemma 15.90.15, commutativity of the square containing `H⁰`.
@[stacks 05EQ "Lemma 15.90.15, H⁰ square"]
#check @LocalizedModule.Away.FormalGluing.h0TensorBaseChange

-- Under the two flatness hypotheses, the `H⁰` comparison is invertible.
@[stacks 05EQ "Lemma 15.90.15, H⁰ comparison isomorphism"]
#check @LocalizedModule.Away.FormalGluing.h0TensorBaseChange_app_isIso
