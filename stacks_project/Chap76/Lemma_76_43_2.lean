/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap76.Lemma_76_43_1_AdicThickening

/-!
# Algebraization of a finite formal algebraic space over a proper first stage

A cartesian successor ladder of algebraic spaces into the adic stages of a
separated finite type morphism over a complete Noetherian affine base, with
finite first stage over `X_1` and proper first stage over `S_1`, algebraizes
to a finite morphism that is proper over the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.43.2: if `A` is Noetherian and `I`-adically complete, `X ⟶ Spec(A)` is a
separated finite type morphism of algebraic spaces, and for `n ≥ 1` one is given algebraic
spaces `Y n` with successor maps over the adic stages `AdicThickening.stage X I n` forming
cartesian squares, such that `Y 1 ⟶ X_1` is finite and `Y 1 ⟶ S_1` is proper, then there
exists a finite morphism `ι : W ⟶ X` with each `Y n` identified with the fibre product of
`W` and `X_n` over `X` via `IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n)`. Pasting
with `isPullback_toAmbient_of_isPullback_ι` recovers the source identification
`Y n = W ×_S S_n`. Moreover `W` is proper over `S`. -/
@[stacks 0A01]
theorem exists_algebraizingFinite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Separated (toBase X)] [FiniteType (toBase X)]
    (Y : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A))) (succ : ∀ n, Y n ⟶ Y (n + 1))
    (toStage : ∀ n, Y n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsFinite (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)] :
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X) (π : ∀ n, Y n ⟶ W),
      IsFinite ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
