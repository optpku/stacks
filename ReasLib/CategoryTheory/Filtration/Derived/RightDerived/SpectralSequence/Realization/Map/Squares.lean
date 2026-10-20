/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality squares for unbounded right-derived realization maps

These bundled `CommSq` views are the structural form of the componentwise computation API.  They
let downstream arguments use the standard categorical square interface without reconstructing
the four sides from the equation lemmas.
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

/-- The first-page naturality equation as a bundled commutative square. -/
@[stacks 0BKK "first-page naturality square"]
theorem pageOneSq
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p q : ℤ) :
    CommSq ((m.sequenceMap.hom 1 zero_le_one).f (p, q))
      (S.pageOneIso p q).hom (T.pageOneIso p q).hom
      (cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) (p + q)) := sorry

/-- The abutment naturality equation as a bundled commutative square. -/
@[stacks 0BKK "abutment naturality square"]
theorem targetSq
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n)
      (S.targetIso n).hom (T.targetIso n).hom
      (cochainCohomologyMap F (FilteredComplex.underlyingMap f) n) := sorry

end SpectralSequence.Realization.Map

end CategoryTheory.FilteredComplex.RightDerived
