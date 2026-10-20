/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.FiniteComponents

/-!
# Finite irreducible components on compact opens after blowup
-/

open AlgebraicGeometry

universe u

/- Lemma 71.17.8: let `S` be a scheme and `X` an algebraic space over `S`.
Let `π` be a chosen blowup of `X` in any closed subspace `Z`. If `X` satisfies
the equivalent conditions of Morphisms of Spaces Lemma 67.49.1, packaged as
`AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X`, then so does
the underlying blowup space `AlgebraicSpace.Blowup.alongSpace Z π`. -/
@[stacks 0BH1] #check
  (AlgebraicGeometry.AlgebraicSpace.Blowup.hasFiniteIrreducibleComponentsOnCompactOpens :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : AlgebraicSpace.ClosedSubspace X)
      (π : AlgebraicSpace.Blowup.along Z)
      [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X],
      AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens
        (AlgebraicSpace.Blowup.alongSpace Z π))
