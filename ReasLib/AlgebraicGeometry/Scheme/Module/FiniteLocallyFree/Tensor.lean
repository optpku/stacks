/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Tensor products of finite locally free scheme modules

This file records preservation of finite local freeness under tensor products and the rank
of a tensor product of modules of fixed rank on a scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank

variable {X : Scheme.{u}}

/-- The tensor product of finite locally free scheme modules of ranks `rE` and `rV` has rank
`rE * rV`. -/
instance tensor
    (ℰ : X.Modules) (rE : ℕ) [IsFiniteLocallyFreeOfRank rE ℰ]
    (𝒱 : X.Modules) (rV : ℕ) [IsFiniteLocallyFreeOfRank rV 𝒱] :
    IsFiniteLocallyFreeOfRank (rE * rV) (ℰ ⊗ 𝒱 : X.Modules) := sorry

end AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank

namespace AlgebraicGeometry.Scheme.Modules

/-- The tensor product of finite locally free modules on a scheme is finite locally free. -/
instance instIsFiniteLocallyFreeTensor {X : Scheme.{u}} (E F : X.Modules)
    [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] :
    (E ⊗ F : X.Modules).IsFiniteLocallyFree :=
  SheafOfModules.IsFiniteLocallyFree.tensor E F

end AlgebraicGeometry.Scheme.Modules
