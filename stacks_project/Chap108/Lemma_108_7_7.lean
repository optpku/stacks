/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Proper
import StacksCheckRecall

/-!
# Lemma 108.7.7

The Hilbert-polynomial algebraic space of closed subschemes, taken with
respect to a relatively ample invertible module, is proper over the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.7.7: if `f : X ⟶ B` is a proper morphism of finite presentation of
algebraic spaces and `L` is an invertible `𝒪_X`-module ample on `X/B` in the
sense of Definition 71.14.1, then the algebraic space `Hilb^P_{X/B}` parametrizing
closed subschemes with Hilbert polynomial `P` with respect to `L` is proper over
`B`. Here `Hilb^P_{X/B}` is the Hilbert-polynomial locus `quotHilbert` of `𝒪_X`. -/
@[stacks 0DPH] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertPolynomial_isProperOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [Proper f] → [FinitePresentation f] → ∀ (L : X.Modules),
      [CategoryTheory.MonoidalCategory.isInvertibleObject L] →
      [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] → ∀ (P : ℤ → ℤ),
        IsProperOver
          (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor)
