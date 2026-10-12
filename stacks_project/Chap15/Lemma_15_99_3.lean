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
# Lemma 15.99.3

@stack 0ATK

Lemma 15.99.3 (Stacks `0ATK`) is the canonical `TensorLeft` comparison criterion.  ReasLib owns
the comparison morphism, its three atomic finiteness criteria, and their disjunctive companion;
this chapter file is only the source-facing recall.
-/

#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_isIso_of_source_isPerfect
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_isIso_of_tensor_isPerfect
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
@[stacks 0ATK "Lemma 15.99.3"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_torAmplitudeGE
