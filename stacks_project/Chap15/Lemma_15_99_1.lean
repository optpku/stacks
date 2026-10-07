module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect

@[expose] public section

/-!
# Lemma 15.99.1

@stack 0A68

Lemma 15.99.1 (Stacks `0A68`) is the canonical `TensorRight` comparison criterion.  ReasLib
owns the comparison morphism, the perfect-source and pseudo-coherent branches, and their
disjunctive companion; the fixed-right tensor model remains explicit in every declaration.
-/

#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_isIso_of_source_isPerfect
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_finiteInjectiveDimension
@[stacks 0A68 "Lemma 15.99.1"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
