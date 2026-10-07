module

import stacks_project.Chap83.Definition_83_9_1_Invariant
import stacks_project.Chap83.Definition_83_9_1_Quotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X)

/- Definition 83.9.1: for a scheme `S`, an algebraic space `B` over `S`, and a pre-relation
`j : R ⟶ U ×_B U`, a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a good quotient
when `φ` is `R`-invariant, affine, and surjective, condition (3) holds universally, and the
functions on `X` are the `R`-invariant functions on `U`. -/
@[stacks 04AC] #check (PreRelation.IsGoodQuotient P φ : Prop)
