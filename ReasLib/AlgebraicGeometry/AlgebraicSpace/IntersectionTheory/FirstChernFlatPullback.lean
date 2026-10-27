/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Flat pullback and first Chern intersection on algebraic spaces

Flat pullback of fixed relative dimension commutes with first Chern intersection
by an invertible module on good algebraic spaces over a universally catenary,
absolutely quasi-separated base equipped with a dimension function.

The construction uses the cycle and Chow theories of algebraic spaces. Extension
to more general ringed sites requires corresponding cycle and rational-equivalence
theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Flat pullback of relative dimension `r` commutes with first Chern intersection
by an invertible module, sending a cycle of degree `k + 1` to a Chow class of
degree `k + r`. -/
theorem flatPullback_firstChernClassCap {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (L : Y.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pY pX δ f r hf k
        (firstChernClassCap pY δ L k α) =
      firstChernClassCap pX δ ((Modules.pullback f).obj L) (k + (r : ℤ))
        (add_right_comm k 1 (r : ℤ) ▸
          flatPullbackHom pY pX δ f r hf (k + 1) α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
