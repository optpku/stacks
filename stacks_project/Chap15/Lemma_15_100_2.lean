module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.ScalarExtension.Perfect

@[expose] public section

/-!
# Lemma 15.100.2

@stack 0A6A

Lemma 15.100.2 (Stacks `0A6A`) recalls the scalar-extension base-change morphism

`RHom_R(K, M) ⊗ᴸ[R] R' ⟶ RHom_R' (K ⊗ᴸ[R] R', M ⊗ᴸ[R] R')`

and its four standard isomorphism cases: `K` perfect; `R'` perfect as an `R`-module; flatness
with `K` pseudo-coherent and `M ∈ D⁺(R)`; or finite Tor dimension with the same boundedness
conditions.  The reusable scalar-extension leaf owns the comparison and all four atomic
invertibility criteria.
-/

/- The concrete comparison morphism from 15.100.1.1. -/
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp

@[stacks 0A6A "Lemma 15.100.2 (1)"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp_isIso_of_source_isPerfect

@[stacks 0A6A "Lemma 15.100.2 (2)"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp_isIso_of_targetRing_isPerfect

@[stacks 0A6A "Lemma 15.100.2 (3)"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp_isIso_of_flat_of_isPseudoCoherent_of_boundedBelow

@[stacks 0A6A "Lemma 15.100.2 (4)"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp_isIso_of_finiteTorDimension_of_isPseudoCoherent_of_boundedBelow

/- The disjunctive convenience form of the four cases. -/
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp_isIso_of_finiteness
