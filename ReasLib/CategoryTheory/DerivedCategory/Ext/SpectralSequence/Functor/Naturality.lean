/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Functor.Filtered
public import ReasLib.CategoryTheory.Filtration.Complex.Quotient.Comparison
public import ReasLib.CategoryTheory.Filtration.Complex.Stage.Naturality

/-!
# Natural transformations for filtered extension groups

This leaf promotes the pointwise stage and quotient maps in `Functor.Filtered` to natural
transformations.  The constructions are obtained by whiskering the neutral filtered-complex
owners, so later spectral-sequence arguments can compose transformations rather than reconstruct
naturality squares object by object.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t v u

namespace CategoryTheory.DerivedCategory.Ext

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Target

/-- The natural Ext transformation induced by comparison of two filtration stages. -/
@[stacks 0G1X "natural Ext transformation between filtration stages"]
noncomputable abbrev stageComparisonNatTrans (M : DerivedCategory A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    stageFunctor M q n ⟶ stageFunctor M p n :=
  Functor.whiskerRight (FilteredComplex.Stage.comparisonNatTrans hpq)
    (DerivedCategory.Q ⋙ functor M n)

/-- A component of `stageComparisonNatTrans` is the pointwise Ext stage-comparison map. -/
@[simp, stacks 0G1X "component of the natural Ext stage comparison"]
theorem stageComparisonNatTrans_app (M : DerivedCategory A) (K : FilteredComplex A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    (stageComparisonNatTrans M hpq n).app K = stageComparisonMap M K hpq n := rfl

/-- Reflexive stage comparison induces the identity natural transformation on Ext. -/
@[simp, stacks 0G1X "identity natural Ext stage comparison"]
theorem stageComparisonNatTrans_refl (M : DerivedCategory A) (p n : ℤ) :
    stageComparisonNatTrans M (le_refl p) n = 𝟙 (stageFunctor M p n) := sorry

/-- Ext stage-comparison natural transformations compose according to transitivity of the
filtration order. -/
@[simp, stacks 0G1X "composition of natural Ext stage comparisons"]
theorem stageComparisonNatTrans_comp (M : DerivedCategory A) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    stageComparisonNatTrans M hqr n ≫ stageComparisonNatTrans M hpq n =
      stageComparisonNatTrans M (hpq.trans hqr) n := sorry

/-- The natural Ext transformation induced by inclusion of a filtration stage into the
underlying complex. -/
@[stacks 0G1X "natural Ext transformation from a filtration stage"]
noncomputable abbrev stageInclusionNatTrans (M : DerivedCategory A) (p n : ℤ) :
    stageFunctor M p n ⟶ filteredFunctor M n :=
  Functor.whiskerRight (FilteredComplex.Stage.inclusionNatTrans p)
    (DerivedCategory.Q ⋙ functor M n)

/-- A component of `stageInclusionNatTrans` is the pointwise Ext stage-inclusion map. -/
@[simp, stacks 0G1X "component of the natural Ext stage inclusion"]
theorem stageInclusionNatTrans_app (M : DerivedCategory A) (K : FilteredComplex A)
    (p n : ℤ) :
    (stageInclusionNatTrans M p n).app K = stageInclusionMap M K p n := rfl

/-- Comparing Ext filtration stages and then including gives the later-stage inclusion. -/
@[simp, stacks 0G1X "factorization of the natural Ext stage inclusion"]
theorem stageComparisonNatTrans_comp_inclusion
    (M : DerivedCategory A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    stageComparisonNatTrans M hpq n ≫ stageInclusionNatTrans M p n =
      stageInclusionNatTrans M q n := sorry

end Target

namespace Source

/-- A component of the source quotient-to-underlying transformation is the pointwise Ext
quotient map. -/
@[simp, stacks 0G1Z "component of the natural source Ext quotient map"]
theorem quotientNatTrans_app (K : DerivedCategory A) (M : (FilteredComplex A)ᵒᵖ)
    (p n : ℤ) :
    (quotientNatTrans K p n).app M = quotientMap M.unop K p n := rfl

/-- The source-Ext map induced by comparison of filtration quotients.

For `p ≤ q`, the complex map is `M / F^q M ⟶ M / F^p M`; contravariance in the first Ext
variable reverses it to the direction displayed here. -/
@[stacks 0G1Z "source Ext comparison between filtration quotients"]
noncomputable abbrev quotientComparisonMap (M : FilteredComplex A)
    (K : DerivedCategory A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    (quotientFunctor K p n).obj (Opposite.op M) ⟶
      (quotientFunctor K q n).obj (Opposite.op M) :=
  ShiftedHom.precomp (DerivedCategory.Q.map (M.quotientComparison hpq)) K n

/-- Quotient comparison of source Ext is the morphism action of the source-variable Ext
functor. -/
@[simp, stacks 0G1Z "functor formula for source Ext quotient comparison"]
theorem quotientComparisonMap_eq_functorMap (M : FilteredComplex A)
    (K : DerivedCategory A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    quotientComparisonMap M K hpq n =
      (functor K n).map (DerivedCategory.Q.map (M.quotientComparison hpq)).op := rfl

/-- Quotient comparisons induce a natural transformation of source-Ext functors. -/
@[stacks 0G1Z "natural source Ext comparison between filtration quotients"]
noncomputable abbrev quotientComparisonNatTrans (K : DerivedCategory A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    quotientFunctor K p n ⟶ quotientFunctor K q n :=
  Functor.whiskerRight (NatTrans.op (FilteredComplex.Quotient.mapOfLE hpq))
    (DerivedCategory.Q.op ⋙ functor K n)

/-- A component of `quotientComparisonNatTrans` is the pointwise source-Ext quotient
comparison. -/
@[simp, stacks 0G1Z "component of the natural source Ext quotient comparison"]
theorem quotientComparisonNatTrans_app (K : DerivedCategory A)
    (M : (FilteredComplex A)ᵒᵖ) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    (quotientComparisonNatTrans K hpq n).app M =
      quotientComparisonMap M.unop K hpq n := rfl

/-- Reflexive filtration-quotient comparison induces the identity on source Ext. -/
@[simp, stacks 0G1Z "identity natural source Ext quotient comparison"]
theorem quotientComparisonNatTrans_refl (K : DerivedCategory A) (p n : ℤ) :
    quotientComparisonNatTrans K (le_refl p) n = 𝟙 (quotientFunctor K p n) := sorry

/-- Source-Ext quotient comparisons compose in increasing filtration-index order. -/
@[simp, stacks 0G1Z "composition of natural source Ext quotient comparisons"]
theorem quotientComparisonNatTrans_comp (K : DerivedCategory A) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    quotientComparisonNatTrans K hpq n ≫ quotientComparisonNatTrans K hqr n =
      quotientComparisonNatTrans K (hpq.trans hqr) n := sorry

/-- Comparing source Ext quotients and then mapping to the underlying complex agrees with the
direct quotient-to-underlying transformation. -/
@[simp, stacks 0G1Z "factorization of the natural source Ext quotient map"]
theorem quotientComparisonNatTrans_comp_toUnderlying
    (K : DerivedCategory A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    quotientComparisonNatTrans K hpq n ≫ quotientNatTrans K q n =
      quotientNatTrans K p n := sorry

end Source

end CategoryTheory.DerivedCategory.Ext
