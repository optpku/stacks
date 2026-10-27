/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LinearSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-! # Chow homotopy invariance for vector bundles on algebraic spaces -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup

/-- Flat pullback along the linear-space projection of a finite locally free module
of rank `r` is bijective on Chow groups, raising degree from `k` to `k + r`. -/
theorem flatPullback_linearSpace_bijective {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) :
    Function.Bijective
      (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pX
        (Modules.linearSpaceπ E ≫ pX) δ (Modules.linearSpaceπ E) r rfl k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowGroup
