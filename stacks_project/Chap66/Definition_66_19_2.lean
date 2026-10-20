/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
import StacksCheckRecall

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
  {xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X}

/- Definition 66.19.2 (1): an étale neighborhood of a geometric point `xbar` of an algebraic
space `X` over a scheme `S` is a commutative triangle `φ : U ⟶ X` of algebraic spaces over `S`
with `φ` étale and a lift of `xbar` to `U`. -/
@[stacks 04JV] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood :
  AlgebraicGeometry.AlgebraicSpace.GeometricPoint X → Type (u + 1))

/- Definition 66.19.2 (2): a morphism of étale neighborhoods `(U, ubar) ⟶ (U', ubar')` is an
`X`-morphism `h : U ⟶ U'` such that `ubar' = h ∘ ubar`. -/
@[stacks 04JV] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Hom :
  AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood xbar →
    AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood xbar → Type (u + 1))
