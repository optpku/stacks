/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Lemma_82_25_1_CyclePullback

/-!
# Flat pullback of Chow classes on algebraic spaces

The Chow-level flat pullback is the descent of the cycle-level operator of
Definition 82.10.1 along rational equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Cycle-level flat pullback carries rational boundaries to rational
boundaries. -/
theorem flatPullbackHom_mem_boundaries {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    RationalEquivalence.boundaries pY δ k ≤
      (RationalEquivalence.boundaries pX δ (k + (r : ℤ))).comap
        (cycleFlatPullback pY pX δ f r hf k) :=
  sorry

/-- Flat pullback of degree-`k` Chow classes along a morphism of relative
dimension `r`. -/
noncomputable def chowFlatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    chowGroup pY δ k →+ chowGroup pX δ (k + (r : ℤ)) :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pY δ k)
    (RationalEquivalence.boundaries pX δ (k + (r : ℤ)))
    (cycleFlatPullback pY pX δ f r hf k)
    (flatPullbackHom_mem_boundaries pY pX δ f r hf k)

/-- Flat pullback of a Chow class is induced by the cycle-level flat
pullback. -/
theorem chowFlatPullback_chowMk {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : cycleGroup pY δ k) :
    chowFlatPullback pY pX δ f r hf k (chowMk pY δ k α) =
      chowMk pX δ (k + (r : ℤ)) (cycleFlatPullback pY pX δ f r hf k α) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
