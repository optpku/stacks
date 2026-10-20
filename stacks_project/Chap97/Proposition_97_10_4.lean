/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Algebraicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

/- Proposition 97.10.4: Let `S` be a scheme. Let `Z ⟶ B` and `X ⟶ B` be morphisms
of algebraic spaces over `S`. If `Z ⟶ B` is finite locally free then
`Mor_B(Z, X)` is an algebraic space. -/
@[stacks 05Y7]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.instIsAlgebraicSpace :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B} [FiniteLocallyFree Z.hom],
      IsAlgebraicSpace (smallFunctor Z X))
