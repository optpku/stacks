/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CoarseQuotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Definition 83.6.1 (1): a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a
coarse quotient of a pre-relation `P` when it is a categorical quotient and an orbit
space. -/
@[stacks 04A2] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCoarseQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
      AlgebraicGeometry.AlgebraicSpace.PreRelation U → (U ⟶ X) → Prop)

/- Definition 83.6.1 (2): if `B = S` and `U`, `R`, `X` are schemes, a morphism of schemes
`φ : U ⟶ X` is a coarse quotient in schemes when it is a categorical quotient in schemes
and an orbit space. -/
@[stacks 04A2] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCoarseQuotientInSchemes :
    ∀ {S : Scheme.{u}} {U X : Over (ofOver (Over.mk (𝟙 S)))},
      AlgebraicGeometry.AlgebraicSpace.PreRelation U → (U ⟶ X) → Prop)
