/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Decomposition
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/-
Lemma 30.12.1: Let `X` be a Noetherian scheme and `ℱ` a coherent `𝒪_X`-module. If the
support of `ℱ` is the union of closed subsets `Z` and `Z'`, then `ℱ` admits a short exact
decomposition whose coherent submodule is supported on `Z'` and whose coherent quotient is
supported on `Z`.
-/
@[stacks 01YD] #check
  (AlgebraicGeometry.Scheme.Modules.exists_shortExact_of_support_eq_union :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (Z Z' : TopologicalSpace.Closeds X)
      (hSupp : RingedSpace.moduleSupport ℱ = (Z : Set X) ∪ (Z' : Set X)),
      ∃ (𝒢' 𝒢 : X.Modules) (h𝒢' : SheafOfModules.IsCoherent 𝒢')
        (h𝒢 : SheafOfModules.IsCoherent 𝒢)
        (ι : 𝒢' ⟶ ℱ) (π : ℱ ⟶ 𝒢) (w : ι ≫ π = 0)
        (hSupp𝒢 : RingedSpace.moduleSupport 𝒢 ⊆ (Z : Set X)),
        (ShortComplex.mk ι π w).ShortExact ∧
          RingedSpace.moduleSupport 𝒢' ⊆ (Z' : Set X))
