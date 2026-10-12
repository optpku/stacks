/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Patching
import stacks_project.Chap10.Lemma_10_77_8.Index
import StacksCheckRecall

/-!
# Lemma 10.77.8

The reusable projective-module patching criterion is owned by `Module.Projective`.

@stack 0H7M
-/

@[expose] public section

@[stacks 0H7M]
#check @Module.Projective.of_quotients_of_inf_eq_bot
