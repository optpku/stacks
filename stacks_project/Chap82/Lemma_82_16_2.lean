/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence
public import stacks_project.Chap82.Lemma_82_11_1_Pullback

/-!
# Flat pullback of rational equivalence on algebraic spaces

In Situation 82.2.1, flat pullback of relative dimension `r` preserves
rational equivalence of cycles on good algebraic spaces over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.16.2: In Situation 82.2.1, let `X, Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. If `α ∼_rat β`
as `k`-cycles on `Y`, then `cycleFlatPullback α ∼_rat cycleFlatPullback β`
as `(k + r)`-cycles on `X`. -/
@[stacks 0EQB]
theorem cycleFlatPullback_rationallyEquivalent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α β : cycleGroup pY δ k)
    (hαβ : RationalEquivalence.RationallyEquivalent pY δ k α β) :
    RationalEquivalence.RationallyEquivalent pX δ (k + (r : ℤ))
      (cycleFlatPullback pY pX δ f r hf k α)
      (cycleFlatPullback pY pX δ f r hf k β) :=
  sorry

/-- Cycle-level flat pullback of relative dimension `r` sends rational
boundaries in degree `k` to rational boundaries in degree `k + r`. -/
theorem cycleFlatPullback_mem_boundaries {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    RationalEquivalence.boundaries pY δ k ≤
      (RationalEquivalence.boundaries pX δ (k + (r : ℤ))).comap
        (cycleFlatPullback pY pX δ f r hf k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
