/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening

/-!
# Algebraization of a formal closed subscheme

A cartesian successor ladder of closed immersions into the adic stages of a
separated finite type morphism over a complete Noetherian affine base
algebraizes to a closed immersion that is proper over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 30.28.1: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)` is
separated of finite type, and for `n ≥ 1` one is given schemes `Z n` with successor maps
over the adic stages `AdicThickening.stage f I n` forming cartesian squares, such that
`Z 1 ⟶ X_1` is a closed immersion and `Z 1 ⟶ S_1` is proper, then there exists a closed
immersion `ι : W ⟶ X` with each `Z n` identified with the fibre product of `W` and `S_n`
over `S`, and moreover `W` is proper over `S`. -/
@[stacks 0899]
theorem exists_algebraizingClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f]
    (Z : ℕ+ → Scheme.{u}) (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage f I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition f I n))
    [IsClosedImmersion (toStage 1)]
    [IsProper (toStage 1 ≫ AdicThickening.toSpec f I 1)] :
    ∃ (W : Scheme.{u}) (ι : W ⟶ X) (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ IsProper (ι ≫ f) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n) :=
  sorry

/-- The over-X cartesian identification of algebraized stages implies the over-S
identification of each `Z n` with the fibre product of `W` and `S_n` over `S`. -/
theorem isPullback_toAmbient_of_isPullback_ι
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) {Z : ℕ+ → Scheme.{u}}
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage f I n)
    {W : Scheme.{u}} (ι : W ⟶ X) (π : ∀ n, Z n ⟶ W)
    (h : ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n)) (n : ℕ+) :
    IsPullback (π n) (toStage n ≫ AdicThickening.toSpec f I n)
      (ι ≫ f) (AdicThickening.toAmbient I n) :=
  sorry

end AlgebraicGeometry.Scheme
