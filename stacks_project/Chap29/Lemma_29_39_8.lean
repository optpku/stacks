/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Tensor
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.39.8: let `f : X ⟶ S` be a finite-type morphism of schemes with quasi-compact
base. If `N` is invertible and `L` is relatively ample, then `N ⊗ Lᵈ` is relatively very
ample for all sufficiently large natural numbers `d`. -/
@[stacks 0FVC] #check
  (AlgebraicGeometry.RelativelyAmple.eventually_relativelyVeryAmple_tensor_tensorPow :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {N L : X.Modules}
      [CompactSpace S] [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [AlgebraicGeometry.Scheme.Modules.Invertible N],
      AlgebraicGeometry.RelativelyAmple f L →
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          AlgebraicGeometry.RelativelyVeryAmple f
            (N ⊗ AlgebraicGeometry.RingedSpace.TensorPower.sheaf L d))
