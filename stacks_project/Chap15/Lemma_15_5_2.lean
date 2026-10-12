/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Pullback.FiniteType

/-!
# Lemma 15.5.2

@stack 08NI

The source-faithful finite-family pullback theorem is owned by
`CategoryTheory.IsPullback.finiteType_pi_of_surjective_of_finiteType`; ReasLib also exposes the
version in which finite type of the common quotient factors is derived from surjectivity.
-/

@[expose] public section

/- @stack 08NI -/
@[stacks 08NI "Lemma 15.5.2"]
#check @CategoryTheory.IsPullback.finiteType_pi_of_surjective_of_finiteType

#check @CategoryTheory.IsPullback.finiteType_pi_of_surjective
