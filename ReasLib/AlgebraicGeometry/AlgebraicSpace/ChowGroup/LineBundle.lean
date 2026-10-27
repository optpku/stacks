/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VectorBundle.LineBundle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-! # Chow homotopy invariance for associated line bundles on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup

/-- Flat pullback along the associated line-bundle projection is bijective on Chow
groups in every integer degree, raising degree by one. -/
theorem flatPullback_bijective_associatedVectorBundle {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (k : ℤ) :
    Function.Bijective
      (flatPullback pX (associatedVectorBundleπ L ≫ pX) δ
        (associatedVectorBundleπ L) 1 rfl k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowGroup
