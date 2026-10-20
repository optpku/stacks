/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Projective

/-!
# Lemma 108.6.1

The Hilbert Quot algebraic space of quotients of `𝒪^{⊕ r}` on projective space
over `Spec(ℤ)` is proper for every rational Hilbert polynomial.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- Lemma 108.6.1: for `n ≥ 0`, `r ≥ 1`, and rational Hilbert polynomial `P`, the algebraic
space `Quot^P` of quotients of `𝒪_{P^n_ℤ}^{⊕ r}` with Hilbert polynomial `P` is
proper over `Spec(ℤ)`. -/
@[stacks 0DPA]
#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbertProjective_isProperOver :
  ∀ (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ),
    IsProperOver (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbertProjective n r P).toFunctor)

