/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic

@[expose] public section

universe u v

/-- Smoothness is equivalent to finite presentation together with lifting across every square-zero quotient. -/
theorem Algebra.smooth_iff_finitePresentation_and_squareZeroLifting
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.Smooth R A ↔ Algebra.FinitePresentation R A ∧
      (∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra R B] (I : Ideal B),
        I ^ 2 = ⊥ →
          Function.Surjective
            ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)) := sorry
