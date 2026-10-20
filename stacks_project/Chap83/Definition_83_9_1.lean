/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GoodQuotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X)

/- Definition 83.9.1: for a scheme `S`, an algebraic space `B` over `S`, and a pre-relation
`j : R ⟶ U ×_B U`, a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a good quotient
when `φ` is `R`-invariant, affine, and surjective, condition (3) holds universally, and the
functions on `X` are the `R`-invariant functions on `U`. -/
@[stacks 04AC] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsGoodQuotient P φ : Prop)
