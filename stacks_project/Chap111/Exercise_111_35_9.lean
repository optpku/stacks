/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineCusp
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.35.9: the tangent space of `Spec (k[x, y] / (x ^ 2 - y ^ 3))`
over `Spec k` at the origin `(0, 0)` has residue-field dimension `2`. -/
@[stacks 029K] #check (AlgebraicGeometry.AffineCusp.tangentDimensionAt_origin :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.Scheme.Hom.tangentDimensionAt
      (AlgebraicGeometry.AffineCusp.toBase k) (AlgebraicGeometry.AffineCusp.origin k) = 2)
