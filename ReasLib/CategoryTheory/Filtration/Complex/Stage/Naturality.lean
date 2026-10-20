module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Stage.Naturality

/-!
# Natural transformations between filtration stages of cochain complexes

This is the cochain-complex facade for the shape-independent natural transformations in
`HomologicalComplex.Filtered.Stage`.  It lets downstream constructions use the familiar
`FilteredComplex` namespace while keeping the neutral homological-complex layer as the data owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Stage

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The natural comparison from the `q`-th filtration-stage complex to the `p`-th one for
`p ≤ q`. -/
@[stacks 012C "natural transformation between filtration stages of cochain complexes"]
abbrev comparisonNatTrans {p q : ℤ} (hpq : p ≤ q) :
    (functor (𝒜 := A) q) ⟶ functor p :=
  HomologicalComplex.Filtered.Stage.comparisonNatTrans
    (c := ComplexShape.up ℤ) hpq

/-- A component of `comparisonNatTrans` is the canonical comparison of stage complexes. -/
@[simp, stacks 012C "component of the cochain-complex stage comparison"]
theorem comparisonNatTrans_app {p q : ℤ} (hpq : p ≤ q) (K : FilteredComplex A) :
    (comparisonNatTrans hpq).app K = K.stageComparison hpq := rfl

/-- The cochain-complex stage comparison associated to reflexivity is the identity natural
transformation. -/
@[simp, stacks 012L "identity natural transformation between cochain-complex stages"]
theorem comparisonNatTrans_refl (p : ℤ) :
    comparisonNatTrans (A := A) (le_refl p) = 𝟙 (functor p) := sorry

/-- Successive cochain-complex stage comparisons compose to the direct comparison. -/
@[simp, stacks 012L "composition of natural transformations between cochain-complex stages"]
theorem comparisonNatTrans_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    comparisonNatTrans (A := A) hqr ≫ comparisonNatTrans hpq =
      comparisonNatTrans (hpq.trans hqr) := sorry

/-- The natural inclusion of the `p`-th filtration-stage complex into the underlying cochain
complex. -/
@[stacks 012C "natural transformation from a cochain-complex stage to the underlying complex"]
abbrev inclusionNatTrans (p : ℤ) :
    (functor (𝒜 := A) p) ⟶ FilteredComplex.underlyingFunctor :=
  HomologicalComplex.Filtered.Stage.inclusionNatTrans
    (c := ComplexShape.up ℤ) p

/-- A component of `inclusionNatTrans` is the canonical stage inclusion. -/
@[simp, stacks 012C "component of the cochain-complex stage inclusion"]
theorem inclusionNatTrans_app (p : ℤ) (K : FilteredComplex A) :
    (inclusionNatTrans p).app K = K.stageInclusion p := rfl

/-- Comparing stages and then including into the underlying cochain complex gives the inclusion
from the later stage. -/
@[simp, stacks 012L "factorization of the cochain-complex stage inclusion"]
theorem comparisonNatTrans_comp_inclusionNatTrans {p q : ℤ} (hpq : p ≤ q) :
    comparisonNatTrans (A := A) hpq ≫ inclusionNatTrans p = inclusionNatTrans q := sorry

end CategoryTheory.FilteredComplex.Stage
