/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/- Exercise 111.33.7: the affine plane `affinePlane k` is an affine scheme, and the open
`puncturedOpen k ⊆ affinePlane k` has open subscheme `(puncturedOpen k).toScheme` that is not
affine. -/
@[stacks 028T] #check (AlgebraicGeometry.PuncturedAffinePlane.affinePlane k : Scheme.{u})
#synth IsAffine (PuncturedAffinePlane.affinePlane k)
@[stacks 028T] #check (AlgebraicGeometry.PuncturedAffinePlane.puncturedOpen k :
  (AlgebraicGeometry.PuncturedAffinePlane.affinePlane k).Opens)
@[stacks 028T] #check (AlgebraicGeometry.PuncturedAffinePlane.not_isAffine k :
  ¬ IsAffine (AlgebraicGeometry.PuncturedAffinePlane.puncturedOpen k).toScheme)
