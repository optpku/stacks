module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.PageTwo
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for truncation-filtration maps

The displayed truncation sequence uses the standard renumbering from page zero.  This leaf exposes
the resulting component directly, so downstream arguments do not need to unfold that construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization.Map

/-- A displayed truncation-sequence page map is the restriction of the original map on the
preceding page. -/
@[simp, stacks 0BKM "page-map computation for truncation-sequence maps"]
theorem sequenceMap_hom
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (r : ℤ) (hr : 2 ≤ r) :
    m.sequenceMap.hom r hr =
      HomologicalComplex.restrictionMap
        (m.original.sequenceMap.hom (r - 1)
          (zero_le_one.trans
            (CohomologicalSpectralSequence.Renumber.one_le_priorPage r hr)))
        (CohomologicalSpectralSequence.Renumber.pageEmbedding r) := sorry

/-- A displayed truncation-sequence component is the original component at the renumbered index. -/
@[simp, stacks 0BKM "component computation for truncation-sequence maps"]
theorem sequenceMap_hom_f
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (r : ℤ) (hr : 2 ≤ r) (ij : ℤ × ℤ) :
    (m.sequenceMap.hom r hr).f ij =
      (m.original.sequenceMap.hom (r - 1)
        (zero_le_one.trans
          (CohomologicalSpectralSequence.Renumber.one_le_priorPage r hr))).f
        (CohomologicalSpectralSequence.Renumber.bidegreeEquiv ij) := sorry

/-- A map of truncation-filtration realizations is zero on every negative second-page column. -/
@[simp, stacks 0BKM "map on a negative truncation-spectral-sequence column"]
theorem pageTwoMap_eq_zero_of_neg
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (i j : ℤ) (hi : i < 0) :
    (m.sequenceMap.hom 2 le_rfl).f (i, j) = 0 := sorry

/-- A map of truncation-filtration realizations is an isomorphism on every negative second-page
column, since both endpoints vanish there. -/
@[stacks 0BKM "isomorphism on a negative truncation-spectral-sequence column"]
theorem pageTwoMap_isIso_of_neg
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (i j : ℤ) (hi : i < 0) :
    IsIso ((m.sequenceMap.hom 2 le_rfl).f (i, j)) := sorry

end Realization.Map

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
