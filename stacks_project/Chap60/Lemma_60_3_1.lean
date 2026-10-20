/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Lemma_60_3_1_SquareZero
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 60.3.1: for a divided power ring `(A, I, γ)` and an `A`-module `M`,
the explicit divided powers on the trivial square-zero extension make the
canonical inclusion a divided-power morphism. -/
@[stacks 07HH] #check
  (DividedPowers.TrivSqZeroExt.inl_isDPMorphism :
    ∀ {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
      [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I),
      DividedPowers.IsDPMorphism gamma
        (DividedPowers.TrivSqZeroExt.dividedPowers M gamma)
        (TrivSqZeroExt.inlHom A M))
