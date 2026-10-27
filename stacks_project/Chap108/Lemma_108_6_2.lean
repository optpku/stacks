/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProjectiveOver

universe u

/- Lemma 108.6.2: the Hilbert Quot algebraic space of a finitely presented sheaf on
`P^n_B`, with rational Hilbert polynomial relative to `𝒪(1)`, is proper over `B`. -/
@[stacks 0DPB] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbertProjectiveOver_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (B : AlgebraicGeometry.AlgebraicSpace S)
      (n : ℕ) (F : (AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace n B).Modules)
      [F.IsFinitePresentation] (P : Polynomial ℚ),
      AlgebraicGeometry.AlgebraicSpace.IsProperOver
        (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbertProjectiveOver n B F P).toFunctor)
