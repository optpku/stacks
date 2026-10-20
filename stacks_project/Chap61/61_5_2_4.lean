/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WLocalHull.Transition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 61.5.2.4: for finite `E₁ ⊆ E₂ ⊆ A`, the canonical `A`-algebra map
`A_{E₁} → A_{E₂}` induces an affine scheme morphism `X_{E₂} ⟶ X_{E₁}`. -/
@[stacks 0972] #check (Algebra.WLocalHull.spectrumMap :
  ∀ {A : Type u} [CommRing A] {E₁ E₂ : Finset A}, E₁ ⊆ E₂ →
    (Algebra.WLocalHull.spectrum A E₂ ⟶ Algebra.WLocalHull.spectrum A E₁))
