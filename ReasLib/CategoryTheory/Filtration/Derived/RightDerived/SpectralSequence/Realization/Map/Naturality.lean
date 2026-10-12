/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of unbounded filtered right-derived realization maps

This file computes first-page and abutment maps through the selected right-derived comparisons.
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

namespace SpectralSequence.Realization

/-- Naturality of the first-page comparison of a right-derived realization map. -/
@[reassoc, stacks 0BKK "naturality of the first page"]
theorem Map.pageOne_hom {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p q : ℤ) :
    (m.sequenceMap.hom 1 zero_le_one).f (p, q) ≫ (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q) := sorry

/-- Naturality of the abutment comparison of a right-derived realization map. -/
@[reassoc, stacks 0BKK "naturality of the abutment"]
theorem Map.target_hom {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        cochainCohomologyMap F (FilteredComplex.underlyingMap f) n := sorry

/-- Inverse naturality of the first-page comparison of a right-derived realization map. -/
@[reassoc, stacks 0BKK "inverse naturality of the first page"]
theorem Map.pageOne_inv_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p q : ℤ) :
    cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q) ≫
        (T.pageOneIso p q).inv =
      (S.pageOneIso p q).inv ≫ (m.sequenceMap.hom 1 zero_le_one).f (p, q) := sorry

/-- Inverse naturality of the abutment comparison of a right-derived realization map. -/
@[reassoc, stacks 0BKK "inverse naturality of the abutment"]
theorem Map.target_inv_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    cochainCohomologyMap F (FilteredComplex.underlyingMap f) n ≫
        (T.targetIso n).inv =
      (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the map on derived graded-piece cohomology by the selected first-page
comparisons recovers the underlying page component. -/
@[reassoc, stacks 0BKK "computation of the first-page map"]
theorem Map.pageOne_naturality_inv {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p q : ℤ) :
    (S.pageOneIso p q).hom ≫
        cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q) ≫
        (T.pageOneIso p q).inv =
      (m.sequenceMap.hom 1 zero_le_one).f (p, q) := sorry

/-- Conjugating the first-page map by the inverse comparisons recovers the derived
graded-piece cohomology map. -/
@[reassoc, stacks 0BKK "target-map computation of the first page"]
theorem Map.pageOne_target_map {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p q : ℤ) :
    (S.pageOneIso p q).inv ≫
        (m.sequenceMap.hom 1 zero_le_one).f (p, q) ≫
      (T.pageOneIso p q).hom =
      cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q) := sorry

/-- Conjugating the derived abutment map by the selected comparisons recovers the homology map
of the filtered model. -/
@[reassoc, stacks 0BKK "computation of the abutment map"]
theorem Map.target_naturality_inv {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).hom ≫
        cochainCohomologyMap F (FilteredComplex.underlyingMap f) n ≫
        (T.targetIso n).inv =
      HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the filtered-model homology map by the inverse comparisons recovers the derived
abutment cohomology map. -/
@[reassoc, stacks 0BKK "target-map computation of the abutment"]
theorem Map.target_map {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
      (T.targetIso n).hom =
      cochainCohomologyMap F (FilteredComplex.underlyingMap f) n := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
