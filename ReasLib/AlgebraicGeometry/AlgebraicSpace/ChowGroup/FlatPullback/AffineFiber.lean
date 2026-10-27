/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-! # Surjectivity of Chow pullback for affine-space fibres -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A quasi-compact flat morphism of relative dimension `r` between good algebraic
spaces over a quasi-separated universally catenary dimensioned base induces a
surjective flat pullback on every Chow group if each residue-field fibre is affine
`r`-space. -/
theorem chowFlatPullback_surjective {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [QuasiCompact f] [Flat f] [RelativeDimension f r]
    [IsDecent Y] (hf : f ≫ pY = pX)
    (h_fiber : ∀ y : Points Y, IsAffineSpaceFiber f r y) (k : ℤ) :
    Function.Surjective (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pY pX δ f r hf k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
