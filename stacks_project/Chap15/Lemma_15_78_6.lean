/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Fiberwise
import StacksCheckRecall

/-!
# Lemma 15.78.6 (09PC)

@stack 09PC

The two regular closed-fiber criteria are owned by the derived-category perfectness leaf. This
Chapter file is their direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.6 (1) (09PC): the closed-fiber homology form. -/
@[stacks 09PC "Lemma 15.78.6 (1)"]
#check @CategoryTheory.isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing

/- Lemma 15.78.6 (2) (09PC): the restriction-of-scalars Tor-amplitude form. -/
@[stacks 09PC "Lemma 15.78.6 (2)"]
#check @CategoryTheory.isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_closedFiber_isRegularLocalRing

#check @CategoryTheory.DerivedCategory.HasTorAmplitudeIn

#print axioms CategoryTheory.isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
