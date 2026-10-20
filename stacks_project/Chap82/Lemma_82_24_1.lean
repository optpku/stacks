/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Definition_71_9_2_RelativeEffectiveCartier
public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import stacks_project.Chap82.Definition_82_22_1_Chow
public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Lemma_82_11_1_Pullback
public import stacks_project.Chap82.Lemma_82_24_1_Pullback

/-!
# Gysin and first Chern class versus restriction to a relative divisor

In Situation 82.2.1, for a flat morphism of relative dimension `r` and a
relative effective Cartier divisor `D`, Gysin after flat pullback agrees with
pullback along `p|_D`, and capping with `c₁(O_X(D))` is the closed pushforward
of that restriction pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.24.1 (1): In Situation 82.2.1 let `X, Y / B` be good. Let
`p : X ⟶ Y` be a flat morphism of relative dimension `r`. Let `i : D ⟶ X` be a
relative effective Cartier divisor, and let `L = O_X(D)`. For any
`α ∈ CH_{k+1}(Y)` one has `i^* (p^* α) = (p|_D)^* α` in `CH_{k+r}(D)`, where
`i^*` is Gysin of `(O_X(D), 1_D)`, `p^*` is cycle-level flat pullback, and
`(p|_D)^*` is relative Cartier pullback. -/
@[stacks 0ERE]
theorem gysin_flatPullback_eq_relativeCartierPullback {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    gysin pX δ (k + (r : ℤ)) D.associatedSheaf D.canonicalSection
        (add_right_comm k 1 (r : ℤ) ▸
          cycleFlatPullback pY pX δ p r hp (k + 1) α) =
      chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (k + (r : ℤ))
        (((congrArg (fun z : ℤ ↦ z - 1)
              (add_right_comm k 1 (r : ℤ))).trans
            (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
          relativeCartierPullback pY pX δ p r hp D (k + 1) α) :=
  sorry

/-- Lemma 82.24.1 (2): In Situation 82.2.1 let `X, Y / B` be good. Let
`p : X ⟶ Y` be a flat morphism of relative dimension `r`. Let `i : D ⟶ X` be a
relative effective Cartier divisor, and let `L = O_X(D)`. For any
`α ∈ CH_{k+1}(Y)` one has `c₁(L) ∩ p^* α = i_* ((p|_D)^* α)` in
`CH_{k+r}(X)`, where `c₁(L) ∩` is first-Chern cap, `p^*` is cycle-level flat
pullback, `(p|_D)^*` is relative Cartier pullback, and `i_*` is closed
pushforward along `Z(1_D)`. -/
@[stacks 0ERE]
theorem firstChernClassCap_flatPullback_eq_pushforward_relativeCartierPullback
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    firstChernClassCap pX δ D.associatedSheaf (k + (r : ℤ))
        (add_right_comm k 1 (r : ℤ) ▸
          cycleFlatPullback pY pX δ p r hp (k + 1) α) =
      chowPushforward pX δ
        (zeroScheme D.associatedSheaf D.canonicalSection) (k + (r : ℤ))
        (chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
          (k + (r : ℤ))
          (((congrArg (fun z : ℤ ↦ z - 1)
                (add_right_comm k 1 (r : ℤ))).trans
              (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
            relativeCartierPullback pY pX δ p r hp D (k + 1) α)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
