/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Retracts
import StacksCheckRecall

/-!
# Direct summands of pseudo-coherent objects

Lemma 15.65.8 (Stacks `064X`) is a direct recall of the reusable retract-stability API in
`CategoryTheory.DerivedCategory.PseudoCoherent.Retracts`.

@stack 064X
-/

@[expose] public section

/- Lemma 15.65.8 (1): the left summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 064X "(1), left biproduct summand"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherent_left_of_biprod

/- Lemma 15.65.8 (2): the right summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 064X "(2), right biproduct summand"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherent_right_of_biprod

/- Lemma 15.65.8 (3): the left summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 064X "(3), left biproduct summand"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherent_left_of_biprod

/- Lemma 15.65.8 (4): the right summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 064X "(4), right biproduct summand"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherent_right_of_biprod

#check @CategoryTheory.DerivedCategory.isMPseudoCoherent_isStableUnderRetracts
#check @CategoryTheory.DerivedCategory.isPseudoCoherent_isStableUnderRetracts

#print axioms CategoryTheory.DerivedCategory.isMPseudoCoherent_isStableUnderRetracts
#print axioms CategoryTheory.DerivedCategory.isPseudoCoherent_isStableUnderRetracts
