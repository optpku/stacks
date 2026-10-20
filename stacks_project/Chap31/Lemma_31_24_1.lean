/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.24.1: if a meromorphic function on a quasi-compact scheme restricts to zero on the
basic open `X_h`, then some power of the image of `h` annihilates it. -/
@[stacks 08I7] #check
  (AlgebraicGeometry.exists_pow_mul_eq_zero_of_meromorphic_restrict_eq_zero :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
        (h : Γ(X, ⊤)) (f : X.toLocallyRingedSpace.meromorphicFunctions),
      f |_ₕ (homOfLE (X.basicOpen_le h)) = 0 →
        ∃ n : ℕ, (X.toLocallyRingedSpace.toMeromorphicFunctions h) ^ n * f = 0)
