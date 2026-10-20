/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.IdealPower
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced

/-!
# Support decompositions of coherent scheme modules

This file records a short exact decomposition of a coherent module whose support is a union of
two closed subsets.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A coherent module whose support is the union of two closed subsets admits a short exact
decomposition into coherent modules supported on the respective subsets. -/
theorem exists_shortExact_of_support_eq_union
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (Z Z' : TopologicalSpace.Closeds X)
    (hSupp : RingedSpace.moduleSupport ℱ = (Z : Set X) ∪ (Z' : Set X)) :
    ∃ (𝒢' 𝒢 : X.Modules) (h𝒢' : SheafOfModules.IsCoherent 𝒢')
      (h𝒢 : SheafOfModules.IsCoherent 𝒢)
      (ι : 𝒢' ⟶ ℱ) (π : ℱ ⟶ 𝒢) (w : ι ≫ π = 0)
      (hSupp𝒢 : RingedSpace.moduleSupport 𝒢 ⊆ (Z : Set X)),
      (ShortComplex.mk ι π w).ShortExact ∧
        RingedSpace.moduleSupport 𝒢' ⊆ (Z' : Set X) := sorry

end AlgebraicGeometry.Scheme.Modules
