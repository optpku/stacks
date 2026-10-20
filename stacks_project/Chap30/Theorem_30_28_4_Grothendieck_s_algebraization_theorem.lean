/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ProperAlgebraization

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u

/- Theorem 30.28.4 (Grothendieck's algebraization theorem)
A cartesian adic ladder with compatible invertible sheaves and proper ample first
stage admits a proper algebraization carrying an ample invertible sheaf. -/
@[stacks 089A] #check (AlgebraicGeometry.Scheme.exists_algebraizingProperAmple :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : ℕ+ → Scheme.{u}) (succ : ∀ n, X n ⟶ X (n + 1))
    (toSpec : ∀ n, X n ⟶ AdicThickening.spec I n)
    (h_pb : ∀ n,
      IsPullback (succ n) (toSpec n) (toSpec (n + 1)) (AdicThickening.specTransition I n))
    (L : ∀ n, (X n).Modules) [∀ n, Modules.Invertible (L n)]
    (φ : ∀ n, (Modules.pullback (succ n)).obj (L (n + 1)) ≅ L n)
    [IsProper (toSpec 1)] [Modules.IsAmple (L 1)],
    ∃ (W : Scheme.{u}) (π : W ⟶ Spec (CommRingCat.of A)) (M : W.Modules)
      (hM : Modules.Invertible M) (e : ∀ n, X n ⟶ W)
      (he : ∀ n, e n = succ n ≫ e (n + 1))
      (ψ : ∀ n, (Modules.pullback (e n)).obj M ≅ L n),
      IsProper π ∧ @Modules.IsAmple W M hM ∧
        (∀ n, IsPullback (e n) (toSpec n) π (AdicThickening.toAmbient I n)) ∧
          sheafIsoCompatible succ L φ M e he ψ)
