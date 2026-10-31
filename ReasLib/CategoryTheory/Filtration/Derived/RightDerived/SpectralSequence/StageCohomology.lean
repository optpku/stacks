/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage cohomology conditions for filtered right-derived functors

This file records the eventual vanishing and stabilization hypotheses used by convergence criteria.
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

namespace StageCohomology

/-- In every degree, the right-derived cohomology of sufficiently high filtration stages
vanishes. -/
@[stacks 0BKK "eventual vanishing of filtered right-derived cohomology"]
def eventuallyVanishesAbove (K : FilteredComplex A) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p → IsZero (cochainCohomology F (K.stage p) n)

/-- In every degree, sufficiently low filtration stages induce isomorphisms on right-derived
cohomology. -/
@[stacks 0BKK "eventual stabilization of filtered right-derived cohomology"]
def eventuallyStabilizesBelow (K : FilteredComplex A) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso (cochainCohomologyMap F (K.stageInclusion p) n)

/-- The specialized vanishing condition is equivalent to the generic stage-cohomology condition
on a chosen filtered right-derived model. -/
@[stacks 0BKK "comparison bridge for eventual vanishing of filtered right-derived cohomology"]
theorem eventuallyVanishesAbove_iff
    {K : FilteredComplex A} (R : KInjectiveResolution K) :
    eventuallyVanishesAbove F K ↔
      FilteredComplex.StageCohomology.eventuallyVanishesAbove (model F R) := sorry

/-- The specialized stabilization condition is equivalent to the generic stage-cohomology
condition on a chosen filtered right-derived model. -/
@[stacks 0BKK "comparison bridge for eventual stabilization of filtered right-derived cohomology"]
theorem eventuallyStabilizesBelow_iff
    {K : FilteredComplex A} (R : KInjectiveResolution K) :
    eventuallyStabilizesBelow F K ↔
      FilteredComplex.StageCohomology.eventuallyStabilizesBelow (model F R) := sorry

end StageCohomology

end CategoryTheory.FilteredComplex.RightDerived
