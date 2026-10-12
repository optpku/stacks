/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap76.Lemma_76_43_1_AdicThickening

/-!
# Algebraization of a formal closed subspace

A cartesian successor ladder of closed immersions into the adic stages of a
separated finite type morphism of algebraic spaces over a complete Noetherian
affine base algebraizes to a closed immersion that is proper over the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.43.1: if `A` is Noetherian and `I`-adically complete, `X` is a
separated finite type algebraic space over `Spec(A)`, and for `n ≥ 1` one is
given algebraic spaces `Z n` with successor maps over the adic stages
`AdicThickening.stage X I n` forming cartesian squares, such that
`Z 1 ⟶ X_1` is a closed immersion and `Z 1 ⟶ S_1` is proper, then there exists
a closed immersion `ι : W ⟶ X` with each `Z n` identified with the fibre
product of `W` and `X_n` over `X`, and moreover `W` is proper over `S`. -/
@[stacks 08BG]
theorem exists_algebraizingClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Separated (toBase X)]
    [FiniteType (toBase X)] (Z : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsClosedImmersion (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)] :
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X)
      (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n) :=
  sorry

/-- The over-X cartesian identification of algebraized stages implies the over-S
identification of each `Z n` with the fibre product of `W` and `S_n` over `S`. -/
theorem isPullback_toAmbient_of_isPullback_ι
    {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A) {Z : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A))}
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage X I n)
    {W : AlgebraicSpace (Spec (CommRingCat.of A))} (ι : W ⟶ X)
    (π : ∀ n, Z n ⟶ W)
    (h : ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n)) (n : ℕ+) :
    IsPullback (π n) (toStage n ≫ AdicThickening.toSpec X I n)
      (ι ≫ toBase X) (AdicThickening.toAmbient I n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
