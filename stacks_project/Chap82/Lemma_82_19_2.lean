/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernFlatPullback
import StacksCheckRecall

/-!
# Flat pullback of first-Chern intersection on algebraic spaces

In Situation 82.2.1, flat pullback of relative dimension `r` commutes with
intersecting a cycle by the first Chern class of an invertible sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.19.2: In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. Let `L` be an
invertible sheaf on `Y`. Let `α` be a `(k + 1)`-cycle on `Y`. Then
`f^*(c1(L) ∩ α) = c1((Modules.pullback f).obj L) ∩ f^* α` in
`chowGroup pX δ (k + (r : ℤ))`. This is the source equality in
`CH_{k+r-1}(X)` for a `k`-cycle, after the Chern-cap indexing
`k_src = k + 1`. The left-hand side uses canonical flat pullback on Chow
groups; the right-hand side caps the pulled-back invertible sheaf against
the cycle-level flat pullback of `α`. -/
@[stacks 0EQR] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_firstChernClassCap :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (L : Y.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)),
    AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pY pX δ f r hf k
        (firstChernClassCap pY δ L k α) =
      firstChernClassCap pX δ ((Modules.pullback f).obj L) (k + (r : ℤ))
        (add_right_comm k 1 (r : ℤ) ▸
          flatPullbackHom pY pX δ f r hf (k + 1) α))
