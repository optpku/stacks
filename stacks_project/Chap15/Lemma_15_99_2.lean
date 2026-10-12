/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect

@[expose] public section

/-!
# Lemma 15.99.2

@stack 0A69

Lemma 15.99.2 (Stacks `0A69`) is the canonical truncation criterion for the `TensorRight`
comparison.  ReasLib owns the comparison and states the finite-injective, finite-Tor, and
pseudo-coherent truncation hypotheses against the explicit fixed-right tensor model.
-/

#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf
@[stacks 0A69 "Lemma 15.99.2"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_isIso_of_finiteInjectiveDimension_of_finiteTorDimension_of_truncLE_isPseudoCoherent
