/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Descent
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Situation 76.56.1: over a scheme `S`, a quasi-compact and quasi-separated algebraic space `X`
is equipped with a chosen affine étale surjection `φ : V ⟶ X`, a commutative factorization
`V ⟶ Y ⟶ X` with `j` an open immersion and `π` finite, and a chosen finite-type quasi-coherent
ideal `I ⊂ 𝒪_Y` whose vanishing locus is the complement of the image of `j`. -/
@[stacks 0GUY] #check (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent.nonempty :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X], Nonempty (ResolutionDescent X))
