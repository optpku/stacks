/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernFundamental

/-!
# Proper pushforward of first Chern intersection on algebraic spaces

Proper pushforward commutes with first Chern intersection of cycles with an
invertible module. Extending this compatibility to more general ringed sites
requires corresponding cycle, divisor, and Chow theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- For a proper morphism of good algebraic spaces over a universally catenary,
quasi-separated base with a dimension function, pushing forward the first Chern
intersection with a pulled-back invertible module equals intersecting the
pushed-forward cycle with that module in the target Chow group. -/
theorem properPushforward_firstChernClassCap {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (L : Y.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup pX δ (k + 1)) :
    ChowGroup.properPushforward pX pY δ f hf k
        (firstChernClassCap pX δ ((Modules.pullback f).obj L) k α) =
      firstChernClassCap pY δ L k
        (properPushforwardHom pX pY δ f hf (k + 1) α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
