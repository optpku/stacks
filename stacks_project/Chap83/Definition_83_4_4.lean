/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.UniversalCategoricalQuotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U) (C : ObjectProperty (Over B))
variable [C.IsClosedUnderLimitsOfShape WalkingCospan]
variable {X : Over B} (φ : U ⟶ X)

/- Definition 83.4.4 (1): in a full subcategory `C` of algebraic spaces over `B`
closed under fibre products, an `R`-invariant morphism `φ : U ⟶ X` in `C` is a
universal categorical quotient in `C` when for every morphism `X' ⟶ X` in `C` the
base change `U' = pullback φ f ⟶ X'` is a categorical quotient in `C` of
`j' = P.baseChange hφ f`. -/
@[stacks 048L] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsUniversalCategoricalQuotient P C φ : Prop)

/- Definition 83.4.4 (2): in a full subcategory `C` of algebraic spaces over `B`
closed under fibre products, an `R`-invariant morphism `φ : U ⟶ X` in `C` is a
uniform categorical quotient in `C` when for every flat morphism `X' ⟶ X` in `C`
the base change `U' = pullback φ f ⟶ X'` is a categorical quotient in `C` of
`j' = P.baseChange hφ f`. -/
@[stacks 048L] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsUniformCategoricalQuotient P C φ : Prop)
