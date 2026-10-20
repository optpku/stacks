/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for truncation-filtration realization maps

The filtered-model component is the canonical input.  This leaf exposes the induced renumbered
spectral-sequence and page-component instances, while source-facing `E₂` and abutment maps are
provided as explicit theorems because their comparison squares carry the realization context.
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

/-- The renumbered spectral-sequence component of an isomorphic truncation realization map is an
isomorphism. -/
@[stacks 0BKM "isomorphism transport for truncation-filtration realization maps"]
noncomputable instance sequenceMap_isIso
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] : IsIso m.sequenceMap := sorry

/-- Every displayed page component of an isomorphic truncation realization map is an isomorphism.
-/
@[stacks 0BKM "page-component isomorphism transport for truncation-filtration realization maps"]
noncomputable instance sequenceMap_f_isIso
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) [IsIso m.filteredMap] :
    IsIso ((m.sequenceMap.hom r hr).f (p, q)) := sorry

/-- The source-facing `E₂` map of an isomorphic truncation realization is an isomorphism. -/
@[stacks 0BKM "second-page map isomorphism for truncation-filtration realization maps"]
theorem pageTwoMap_isIso_of_filteredMap
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (i : ℕ) (j : ℤ) [IsIso m.filteredMap] :
    IsIso ((F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f)) := sorry

/-- The source-facing abutment map of an isomorphic truncation realization is an isomorphism. -/
@[stacks 0BKM "abutment map isomorphism for truncation-filtration realization maps"]
theorem targetMap_isIso_of_filteredMap
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (n : ℤ) [IsIso m.filteredMap] :
    IsIso ((Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f) := sorry

/-- A truncation-filtration realization map is an isomorphism from the second page whenever all
cohomology maps of its filtered graded pieces are isomorphisms. -/
@[stacks 0BKM "filtered graded-piece comparison criterion for truncation realizations"]
theorem isIsoFromFiltered
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ (p q : ℤ),
      IsIso (HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap m.filteredMap p) (p + q))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 2 le_rfl := sorry

/-- A truncation-filtration realization map is an isomorphism from the second page when its whole
filtered-model component is an isomorphism. -/
@[stacks 0BKM "filtered-map isomorphism criterion for truncation realizations"]
theorem isIsoFromFilteredMap
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 2 le_rfl := sorry

/-- A truncation-filtration realization map is an isomorphism from the second page whenever all
source-facing second-page right-derived maps are isomorphisms. -/
@[stacks 0BKM "second-page comparison criterion for truncation-filtration realizations"]
theorem isIsoFrom
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ (i : ℕ) (j : ℤ),
      IsIso ((F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 2 le_rfl := sorry

/-- Every truncation-filtration realization map over an identity is an isomorphism from the
second page onward. -/
@[stacks 0BKM "independence of truncation-filtration realizations"]
theorem isIsoFromTwo
    {K : DerivedCategory A} {S T : Realization F K}
    (m : Map F (𝟙 K) S T) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 2 le_rfl := sorry

variable {K L : DerivedCategory A} {f : K ⟶ L}
variable {S : Realization F K} {T : Realization F L}
variable (m : Map F f S T) [IsIso m.filteredMap]

#synth IsIso (CohomologicalSpectralSequence.Renumber.FromZero.map m.original.sequenceMap)
#synth IsIso m.sequenceMap
#synth IsIso ((m.sequenceMap.hom 2 le_rfl).f (0, 0))

end Realization.Map

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
