/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.WeightedPolynomial
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.37.7 (1): the degree-one twist on the weighted projective spectrum of
`k[x, y, z]` with weights `(1, 2, 3)` is not invertible. -/
@[stacks 02A3] #check (AlgebraicGeometry.Proj.Weights123.twistOne_not_invertible :
  ∀ (k : Type u) [Field k],
    ¬ AlgebraicGeometry.Scheme.Modules.Invertible
      (AlgebraicGeometry.Proj.Weights123.twist k 1))

/- Exercise 111.37.7 (2): the degree-one twist on the weighted projective spectrum of
`k[x, y]` with weights `(1, 2)` is invertible, but its squared multiplication is not an
isomorphism. -/
@[stacks 02A3] #check (AlgebraicGeometry.Proj.Weights12.twistOne_invertible_mul_not_iso :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.Scheme.Modules.Invertible
      (AlgebraicGeometry.Proj.Weights12.twist k 1) ∧
    ¬ CategoryTheory.IsIso (AlgebraicGeometry.Proj.Weights12.mulOneOne k))
