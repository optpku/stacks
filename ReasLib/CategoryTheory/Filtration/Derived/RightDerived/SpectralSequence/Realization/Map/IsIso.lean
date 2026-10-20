/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for unbounded filtered right-derived realization maps

The filtered-model component is the canonical input for isomorphism transport.  This leaf exposes
the induced spectral-sequence and page-component instances without introducing a second map owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization.Map

/-- The spectral-sequence component of an isomorphic right-derived realization map is an
isomorphism. -/
@[stacks 0BKK "isomorphism transport for unbounded right-derived realization maps"]
noncomputable instance sequenceMap_isIso
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] : IsIso m.sequenceMap := sorry

/-- Every page component of an isomorphic right-derived realization map is an isomorphism. -/
@[stacks 0BKK "page-component isomorphism transport for unbounded right-derived realization maps"]
noncomputable instance sequenceMap_f_isIso
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) [IsIso m.filteredMap] :
    IsIso ((m.sequenceMap.hom r hr).f (p, q)) := sorry

/-- The source-facing first-page map is an isomorphism when the filtered component is. -/
@[stacks 0BKK "first-page target isomorphism from a filtered isomorphism"]
theorem pageOneMap_isIso_of_filteredMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (p q : ℤ) [IsIso m.filteredMap] :
    IsIso (cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q)) := sorry

/-- The source-facing abutment map is an isomorphism when the filtered component is. -/
@[stacks 0BKK "abutment target isomorphism from a filtered isomorphism"]
theorem targetMap_isIso_of_filteredMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (n : ℤ) [IsIso m.filteredMap] :
    IsIso (cochainCohomologyMap F (FilteredComplex.underlyingMap f) n) := sorry

/-- A right-derived realization map is an isomorphism from the first page whenever the
associated-graded cohomology maps of its internal filtered-model component are isomorphisms. -/
@[stacks 0BKK "filtered-model comparison criterion for right-derived realizations"]
theorem isIsoFromFiltered
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ p q : ℤ,
      IsIso (HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap m.filteredMap p) (p + q))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- A right-derived realization map is an isomorphism from the first page when its whole
filtered-model component is an isomorphism. -/
@[stacks 0BKK "filtered-map isomorphism criterion for right-derived realizations"]
theorem isIsoFromFilteredMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    [IsIso m.filteredMap] :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- A right-derived realization map is an isomorphism from the first page whenever all
source-facing graded-piece cohomology maps are isomorphisms. -/
@[stacks 0BKK "page-one comparison criterion for right-derived realizations"]
theorem isIsoFrom
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T)
    (hpage : ∀ p q : ℤ,
      IsIso (cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q))) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

/-- Every right-derived realization map over an identity is an isomorphism from the first page
onward. -/
@[stacks 0BKK "independence of right-derived realizations"]
theorem isIsoFromOne
    {K : FilteredComplex A} {S T : Realization F K}
    (m : Map F (𝟙 K) S T) :
    SpectralSequence.Hom.IsIsoFrom m.sequenceMap 1 zero_le_one := sorry

variable {K L : FilteredComplex A} {f : K ⟶ L}
variable {S : Realization F K} {T : Realization F L}
variable (m : Map F f S T) [IsIso m.filteredMap]

#synth IsIso m.sequenceMap
#synth IsIso ((m.sequenceMap.hom 1 zero_le_one).f (0, 0))

end SpectralSequence.Realization.Map

end CategoryTheory.FilteredComplex.RightDerived
