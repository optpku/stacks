/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.27.3: Let `X` be a scheme. If a set of global sections generates the unit ideal
and every corresponding basic open is affine, then `X` is affine. -/
@[stacks 01QF] #check
  (AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen :
    ∀ {X : Scheme.{u}} (s : Set Γ(X, ⊤)), Ideal.span s = ⊤ →
      (∀ i ∈ s, IsAffineOpen (X.basicOpen i)) → IsAffine X)
