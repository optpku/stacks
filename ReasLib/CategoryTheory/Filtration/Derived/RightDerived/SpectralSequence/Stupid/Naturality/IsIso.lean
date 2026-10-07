module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Comparison
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for stupid-filtration realization maps

The generic filtered realization map owns the filtered-model isomorphism transport.  This leaf
registers the corresponding instances for the stupid-filtration wrapper and exposes the
source-facing first-page and abutment maps without adding global instances for those target maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization.Map

/-- An isomorphic filtered component induces an isomorphic stupid-filtration spectral-sequence map. -/
@[stacks 0FLK "isomorphism transport for stupid-filtration realization maps"]
noncomputable instance sequenceMap_isIso
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] : IsIso m.sequenceMap := sorry

/-- Every page component of an isomorphic stupid-filtration realization map is an isomorphism. -/
@[stacks 0FLK "page-component isomorphism transport for stupid-filtration maps"]
noncomputable instance sequenceMap_f_isIso
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) [IsIso m.filteredMap] :
    IsIso ((m.sequenceMap.hom r hr).f (p, q)) := sorry

/-- The source-facing first-page map is an isomorphism when the filtered component is. -/
@[stacks 0FLK "first-page target isomorphism from a filtered isomorphism"]
theorem pageOneMap_isIso_of_filteredMap
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (p : ℤ) (q : ℕ) [IsIso m.filteredMap] :
    IsIso ((F.rightDerived q).map (f.f p)) := sorry

/-- The source-facing abutment map is an isomorphism when the filtered component is. -/
@[stacks 0FLK "abutment target isomorphism from a filtered isomorphism"]
theorem targetMap_isIso_of_filteredMap
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (n : ℤ) [IsIso m.filteredMap] :
    IsIso (Functor.RightDerived.Homotopy.cochainCohomologyMap F f n) := sorry

/-- A stupid-filtration realization map is an isomorphism from the first page whenever all
cohomology maps of its filtered graded pieces are isomorphisms. -/
@[stacks 0FLK "filtered graded-piece comparison criterion for stupid-filtration realizations"]
theorem isIsoFromFiltered
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ (p q : ℤ),
      IsIso (HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap m.filteredMap p) (p + q))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- A stupid-filtration realization map is an isomorphism from the first page when its whole
filtered-model component is an isomorphism. -/
@[stacks 0FLK "filtered-map isomorphism criterion for stupid-filtration realizations"]
theorem isIsoFromFilteredMap
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- A stupid-filtration realization map is an isomorphism from the first page whenever all
source-facing first-page right-derived maps are isomorphisms. -/
@[stacks 0FLK "first-page comparison criterion for stupid-filtration realizations"]
theorem isIsoFrom
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ (p : ℤ) (q : ℕ), IsIso ((F.rightDerived q).map (f.f p))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- Every stupid-filtration realization map over an identity is an isomorphism from the first
page onward. -/
@[stacks 0FLK "independence of stupid-filtration realizations"]
theorem isIsoFromOne
    {K : CochainComplex A ℤ} {S T : Realization F K}
    (m : Map F (𝟙 K) S T) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

end Realization.Map

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
