/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.16.2. Flat pullback of relative dimension `r` preserves rational
equivalence of cycles on good algebraic spaces over `B`. -/
@[stacks 0EQB] #check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullbackHom_rationallyEquivalent :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α β : cycleGroup pY δ k)
    (hαβ : RationalEquivalence.RationallyEquivalent pY δ k α β),
    RationalEquivalence.RationallyEquivalent pX δ (k + (r : ℤ))
      (flatPullbackHom pY pX δ f r hf k α)
      (flatPullbackHom pY pX δ f r hf k β))

#check (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback_mem_boundaries :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ),
    RationalEquivalence.boundaries pY δ k ≤
      (RationalEquivalence.boundaries pX δ (k + (r : ℤ))).comap
        (flatPullbackHom pY pX δ f r hf k))
