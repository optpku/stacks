/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteAlgebraization

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/- Lemma 76.43.2: A cartesian adic ladder with finite first stage proper over the
quotient base algebraizes to a finite morphism proper over the complete base. -/
@[stacks 0A01] #check (AlgebraicGeometry.AlgebraicSpace.exists_algebraizingFinite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Separated (toBase X)] [FiniteType (toBase X)]
    (Y : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A))) (succ : ∀ n, Y n ⟶ Y (n + 1))
    (toStage : ∀ n, Y n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsFinite (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)],
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X) (π : ∀ n, Y n ⟶ W),
      IsFinite ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n))
