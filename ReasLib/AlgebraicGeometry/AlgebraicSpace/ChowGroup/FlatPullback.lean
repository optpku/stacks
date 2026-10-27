/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback

/-! # Flat pullback on Chow groups of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
  (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
  (hf : f ≫ pY = pX) (k : ℤ)

/-- Flat pullback of cycles carries rational boundaries to rational boundaries. -/
theorem flatPullback_mem_boundaries :
    RationalEquivalence.boundaries pY δ k ≤
      (RationalEquivalence.boundaries pX δ (k + r)).comap
        (Hom.flatPullbackHom pY pX δ f r hf k) := sorry

/-- Flat pullback on Chow groups raises degree by the relative dimension. -/
def flatPullback : Hom.chowGroup pY δ k →+ Hom.chowGroup pX δ (k + r) :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pY δ k) (RationalEquivalence.boundaries pX δ (k + r))
    (Hom.flatPullbackHom pY pX δ f r hf k)
    (flatPullback_mem_boundaries pY pX δ f r hf k)

/-- Pulling back the class of a cycle gives the class of its flat cycle pullback. -/
theorem flatPullback_chowMk (α : Hom.cycleGroup pY δ k) :
    flatPullback pY pX δ f r hf k (Hom.chowMk pY δ k α) =
      Hom.chowMk pX δ (k + r) (Hom.flatPullbackHom pY pX δ f r hf k α) := sorry

end AlgebraicGeometry.AlgebraicSpace.ChowGroup

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Flat pullback along a morphism of relative dimension `r` preserves rational
equivalence of cycles, raising their degree from `k` to `k + r`. -/
theorem flatPullbackHom_rationallyEquivalent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α β : cycleGroup pY δ k)
    (hαβ : RationalEquivalence.RationallyEquivalent pY δ k α β) :
    RationalEquivalence.RationallyEquivalent pX δ (k + (r : ℤ))
      (flatPullbackHom pY pX δ f r hf k α)
      (flatPullbackHom pY pX δ f r hf k β) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
