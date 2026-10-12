/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence

/-!
# Proper pushforward of rational equivalence on algebraic spaces

In Situation 82.2.1, proper pushforward of cycles on good algebraic spaces
over `B` preserves rational equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.16.3: In Situation 82.2.1, let `X, Y / B` be good. Let
`p : X ⟶ Y` be a proper morphism. If `α ∼_rat β` as `k`-cycles on `X`, then
`properPushforwardHom α ∼_rat properPushforwardHom β` as `k`-cycles on `Y`. -/
@[stacks 0EQC]
theorem properPushforwardHom_rationallyEquivalent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) [Proper p] (hp : p ≫ pY = pX) (k : ℤ)
    (α β : cycleGroup pX δ k)
    (hαβ : RationalEquivalence.RationallyEquivalent pX δ k α β) :
    RationalEquivalence.RationallyEquivalent pY δ k
      (properPushforwardHom pX pY δ p hp k α)
      (properPushforwardHom pX pY δ p hp k β) :=
  sorry

/-- Cycle-level proper pushforward sends rational boundaries in degree `k` on
`X` to rational boundaries in degree `k` on `Y`. -/
theorem properPushforwardHom_mem_boundaries {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) [Proper p] (hp : p ≫ pY = pX) (k : ℤ) :
    RationalEquivalence.boundaries pX δ k ≤
      (RationalEquivalence.boundaries pY δ k).comap
        (properPushforwardHom pX pY δ p hp k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
