/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.PseudoDivisor

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Compatibility check for pseudo-divisor intersection after its migration to the reusable
Chow-group owner. -/
#check (AlgebraicGeometry.Scheme.PseudoDivisor.intersectionSupported :
  ∀ {S X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ S)
    [AlgebraicGeometry.UniversallyCatenary S] [AlgebraicGeometry.LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : AlgebraicGeometry.Scheme.PseudoDivisor X) (k : ℤ),
    AlgebraicGeometry.ChowGroup.Supported p δ (k + 1) →
      AlgebraicGeometry.ChowGroup.Supported p δ k)
