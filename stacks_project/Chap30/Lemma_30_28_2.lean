/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.FiniteAlgebraization

/-!
# Algebraization of a finite formal scheme over a proper first stage

A cartesian successor ladder of finite morphisms into the adic stages of a
separated finite type morphism over a complete Noetherian affine base, with
proper first stage over `S_1`, algebraizes to a finite morphism that is proper
over the base.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

/- Lemma 30.28.2: the compatible finite adic tower algebraizes to a finite
morphism proper over the complete Noetherian base. The projection compatibility
recovers the identifications over each `X_n` from the canonical pullback stages. -/
@[stacks 09ZT] #check
  (AlgebraicGeometry.Scheme.exists_algebraizingFinite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (Y : ℕ+ → AlgebraicGeometry.Scheme.{u})
      (successor : ∀ (n : ℕ+), Y n ⟶ Y (n + 1))
      (toX : ∀ (n : ℕ+), Y n ⟶ X)
      (toBase : ∀ (n : ℕ+), Y n ⟶
        AlgebraicGeometry.Spec (CommRingCat.of (A ⧸ I ^ (n : ℕ))))
      (h_over : ∀ (n : ℕ+), toX n ≫ f = toBase n ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n : ℕ)))))
      (h_transition : ∀ (n : ℕ+), successor n ≫ toX (n + 1) = toX n)
      (h_cartesian : ∀ (n : ℕ+), CategoryTheory.IsPullback (successor n) (toBase n)
        (toBase (n + 1))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n : ℕ)))))
      (h_finite : ∀ (n : ℕ+),
        AlgebraicGeometry.IsFinite
          (CategoryTheory.Limits.pullback.lift (toX n) (toBase n) (h_over n)))
      (h_proper : AlgebraicGeometry.IsProper (toBase 1)),
      ∃ (W : AlgebraicGeometry.Scheme.{u}) (inclusion : W ⟶ X)
        (comparison : ∀ n, Y n ⟶ W),
        AlgebraicGeometry.IsFinite inclusion ∧
          AlgebraicGeometry.IsProper (inclusion ≫ f) ∧
          (∀ (n : ℕ+), comparison n ≫ inclusion = toX n) ∧
          (∀ (n : ℕ+), successor n ≫ comparison (n + 1) = comparison n) ∧
          (∀ (n : ℕ+), CategoryTheory.IsPullback (comparison n) (toBase n)
            (inclusion ≫ f)
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ)))))))
