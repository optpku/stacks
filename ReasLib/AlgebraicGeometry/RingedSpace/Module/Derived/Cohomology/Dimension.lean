/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension

@[expose] public section

/-!
# Cohomological dimension of module sections

This module specializes the functorial cohomological-dimension API to module-valued sections on
an open subset of a ringed space.  The top-open specialization is the corresponding global
module-cohomological dimension of the ringed space.
-/

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace ModuleCohomology

/-- Module sections on `U` have cohomological dimension at most `d`. -/
@[stacks 0F5Z "cohomological-dimension bound"]
abbrev HasDimensionLE (X : RingedSpace.{u}) (U : Opens X.carrier) (d : ℤ) : Prop :=
  (moduleSectionsEvaluationFunctor X U).HasCohomologicalDimensionLE d

/-- Module sections on `U` have a uniform finite cohomological-dimension bound. -/
@[stacks 0F5Z "finite-dimensionality hypothesis",
  stacks 09J7 "(2), top-open specialization"]
abbrev HasFiniteDimension (X : RingedSpace.{u}) (U : Opens X.carrier) : Prop :=
  (moduleSectionsEvaluationFunctor X U).HasFiniteCohomologicalDimension

/-- Every module-cohomology functor on `U` preserves coproducts. -/
@[stacks 0F5Z "coproduct hypothesis"]
abbrev PreservesCoproducts (X : RingedSpace.{u}) (U : Opens X.carrier) : Prop :=
  (moduleSectionsEvaluationFunctor X U).PreservesCoproductsOfRightDerived

/-- A bound on module cohomology over `U`, expanded in terms of the canonical cohomology
objects. -/
theorem hasDimensionLE_iff (X : RingedSpace.{u}) (U : Opens X.carrier) (d : ℤ) :
    HasDimensionLE X U d ↔
      ∀ p : ℕ, d < (p : ℤ) → ∀ F : X.Modules,
        IsZero (moduleCohomologyAtOpen U F p) := sorry

/-- Finite module-cohomological dimension over `U`, expanded as a uniform vanishing bound. -/
theorem hasFiniteDimension_iff (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasFiniteDimension X U ↔
      ∃ d : ℤ, ∀ p : ℕ, d < (p : ℤ) → ∀ F : X.Modules,
        IsZero (moduleCohomologyAtOpen U F p) := sorry

/-- The coproduct property expanded degreewise for the canonical module-cohomology functors. -/
theorem preservesCoproducts_iff (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesCoproducts X U ↔
      ∀ (p : ℕ) (I : Type u),
        PreservesColimitsOfShape (Discrete I)
          (moduleCohomologyAtOpenFunctor X U p) := sorry

end ModuleCohomology

namespace Module

/-- A ringed space has finite module-cohomological dimension when module sections on its top
open have a uniform finite cohomological-dimension bound. -/
@[stacks 09J7 "(2), finite cohomological dimension"]
abbrev HasFiniteCohomologicalDimension (X : RingedSpace.{u}) : Prop :=
  ModuleCohomology.HasFiniteDimension X (⊤ : Opens X.carrier)

/-- Global finite module-cohomological dimension, expanded in terms of top-open cohomology. -/
theorem hasFiniteCohomologicalDimension_iff (X : RingedSpace.{u}) :
    HasFiniteCohomologicalDimension X ↔
      ∃ d : ℤ, ∀ p : ℕ, d < (p : ℤ) → ∀ F : X.Modules,
        IsZero (moduleCohomologyAtOpen (⊤ : Opens X.carrier) F p) := sorry

end Module

end AlgebraicGeometry.RingedSpace
