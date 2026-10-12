/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Views
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.StageCohomology
public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Convergence of unbounded filtered right-derived realizations

Stagewise vanishing and stabilization imply boundedness, finite abutment filtrations, and convergence.
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

/-- Stagewise vanishing and stabilization make a right-derived realization bounded. -/
@[stacks 0BKK "boundedness of an unbounded filtered right-derived spectral sequence"]
theorem isBounded {K : FilteredComplex A} (S : Realization F K)
    (hvanish : StageCohomology.eventuallyVanishesAbove F K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow F K) :
    S.sequence.IsBounded := sorry

/-- Stagewise vanishing and stabilization make the induced cohomology filtrations finite. -/
@[stacks 0BKK "finite filtration from an unbounded filtered right-derived spectral sequence"]
theorem finite {K : FilteredComplex A} (S : Realization F K)
    (hvanish : StageCohomology.eventuallyVanishesAbove F K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow F K) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Stagewise vanishing and stabilization imply convergence of a right-derived realization. -/
@[stacks 0BKK "convergence of an unbounded filtered right-derived spectral sequence"]
theorem converges {K : FilteredComplex A} (S : Realization F K)
    (hvanish : StageCohomology.eventuallyVanishesAbove F K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow F K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

/-- Generic model stage criteria imply boundedness of the right-derived realization. -/
@[stacks 0BKK "generic-model boundedness of an unbounded filtered right-derived realization"]
theorem isBounded_of_generic {K : FilteredComplex A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (model F S.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (model F S.resolution)) :
    S.sequence.IsBounded := sorry

/-- Generic model stage criteria imply finite abutment filtrations of the realization. -/
@[stacks 0BKK "generic-model finite filtration of an unbounded filtered right-derived realization"]
theorem finite_of_generic {K : FilteredComplex A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (model F S.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (model F S.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Generic model stage criteria imply convergence of the right-derived realization. -/
@[stacks 0BKK "generic-model convergence of an unbounded filtered right-derived realization"]
theorem converges_of_generic {K : FilteredComplex A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (model F S.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (model F S.resolution)) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
