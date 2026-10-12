/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import ReasLib.CategoryTheory.Filtration.Complex.Quotient.Map
public import ReasLib.CategoryTheory.Filtration.Complex.Quotient.IsIso
public import ReasLib.CategoryTheory.Filtration.Quotient.Comparison

/-!
# Comparisons between quotients of filtered complexes

This file lifts the category-independent comparison between filtration quotients degreewise to
filtered cochain complexes. The resulting API is independent of derived categories and can be
reused by Ext, spectral-sequence, and completion constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Quotient

/-- Projection from the underlying complex to quotient by `F^p`, natural in the filtered
complex. -/
@[stacks 0BKI "projection to a filtered-complex quotient"]
abbrev fromUnderlying (p : ℤ) :
    (underlyingFunctor : FilteredComplex A ⥤ CochainComplex A ℤ) ⟶ quotientFunctor p :=
  NatTrans.mapHomologicalComplex (FilteredObject.Quotient.fromForget p) (ComplexShape.up ℤ)

/-- For `p ≤ q`, the natural transformation from quotient by `F^q` to quotient by `F^p`. -/
@[stacks 0BKI "comparison between filtered-complex quotients"]
abbrev mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (quotientFunctor q : FilteredComplex A ⥤ CochainComplex A ℤ) ⟶ quotientFunctor p :=
  NatTrans.mapHomologicalComplex (FilteredObject.Quotient.mapOfLE hpq) (ComplexShape.up ℤ)

/-- The component of the natural quotient projection is `underlyingToQuotient`. -/
@[simp, stacks 0BKI "component of the filtered-complex quotient projection"]
theorem fromUnderlying_app (K : FilteredComplex A) (p : ℤ) :
    (fromUnderlying p).app K = K.underlyingToQuotient p := sorry

/-- Natural quotient projections are compatible with comparison of filtration indices. -/
@[stacks 0BKI "factorization of the natural filtered-complex quotient projection"]
theorem fromUnderlying_comp_mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (fromUnderlying q :
      (underlyingFunctor : FilteredComplex A ⥤ CochainComplex A ℤ) ⟶ quotientFunctor q) ≫
        mapOfLE hpq = fromUnderlying p := sorry

end Quotient

/-- The canonical comparison `K / F^q K ⟶ K / F^p K` for `p ≤ q`. -/
@[stacks 0BKI "comparison map between filtered-complex quotients"]
abbrev quotientComparison (K : FilteredComplex A) {p q : ℤ} (hpq : p ≤ q) :
    K.quotient q ⟶ K.quotient p :=
  (Quotient.mapOfLE hpq).app K

/-- The comparison between filtered-complex quotients is computed degreewise by the comparison
between filtered-object quotients. -/
@[simp, stacks 0BKI "degreewise formula for filtered-complex quotient comparison"]
theorem quotientComparison_f (K : FilteredComplex A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    (K.quotientComparison hpq).f n =
      FilteredObject.Quotient.comparison (K.X n) hpq := rfl

/-- The comparison from a filtered-complex quotient to itself is the identity. -/
@[simp, stacks 0BKI "identity comparison between filtered-complex quotients"]
theorem quotientComparison_refl (K : FilteredComplex A) (p : ℤ) :
    K.quotientComparison (le_refl p) = 𝟙 (K.quotient p) := sorry

/-- Successive filtered-complex quotient comparisons compose to the direct comparison. -/
@[stacks 0BKI "composition of filtered-complex quotient comparisons"]
theorem quotientComparison_comp (K : FilteredComplex A) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    K.quotientComparison hqr ≫ K.quotientComparison hpq =
      K.quotientComparison (hpq.trans hqr) := sorry

/-- A filtered-complex morphism commutes with comparisons between filtration quotients. -/
@[reassoc, stacks 0BKI "naturality of filtered-complex quotient comparison"]
theorem quotientComparison_naturality {K L : FilteredComplex A} (f : K ⟶ L)
    {p q : ℤ} (hpq : p ≤ q) :
    K.quotientMap f q ≫ L.quotientComparison hpq =
      K.quotientComparison hpq ≫ K.quotientMap f p := sorry

/-- Projection to `K / F^p K` factors through every later quotient `K / F^q K`. -/
@[stacks 0BKI "factorization of a filtered-complex quotient projection"]
theorem underlyingToQuotient_comp_quotientComparison (K : FilteredComplex A)
    {p q : ℤ} (hpq : p ≤ q) :
    K.underlyingToQuotient q ≫ K.quotientComparison hpq =
      K.underlyingToQuotient p := sorry

end CategoryTheory.FilteredComplex
