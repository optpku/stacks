module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for stupid-filtration maps

The first page of a stupid-filtration realization vanishes in negative cohomological rows.  This
leaf exposes the corresponding map computation and isomorphism criterion directly.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Map

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- A stupid-filtration realization map is zero on every negative first-page row. -/
@[simp, stacks 0FLK "map on a negative stupid-spectral-sequence row"]
theorem pageOneMap_eq_zero_of_neg
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (p q : ℤ) (hq : q < 0) :
    (m.sequenceMap.hom 1 zero_le_one).f (p, q) = 0 := sorry

/-- A stupid-filtration realization map is an isomorphism on every negative first-page row,
since both endpoints vanish there. -/
@[stacks 0FLK "isomorphism on a negative stupid-spectral-sequence row"]
theorem pageOneMap_isIso_of_neg
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (p q : ℤ) (hq : q < 0) :
    IsIso ((m.sequenceMap.hom 1 zero_le_one).f (p, q)) := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Map
