module

import stacks_project.Chap83.Definition_83_4_1_Invariant
import stacks_project.Chap83.Definition_83_4_1_Quotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace ObjectProperty

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
variable (φ : U ⟶ X)
variable (C : ObjectProperty (Over B))

/- Definition 83.4.1 (1): a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a
categorical quotient of a pre-relation `P` when it is `R`-invariant and every
`R`-invariant morphism `ψ : U ⟶ Y` factors uniquely as `ψ = φ ≫ χ`. -/
@[stacks 048J] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotient P φ : Prop)

/- Definition 83.4.1 (2): a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a
categorical quotient in a full subcategory `C` when `U`, `R`, and `X` lie in `C`, `φ`
is `R`-invariant, and every `R`-invariant morphism in `C` factors uniquely through
`φ`. -/
@[stacks 048J] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P C φ : Prop)

variable {U₀ X₀ : Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S)))}
variable (P₀ : AlgebraicGeometry.AlgebraicSpace.PreRelation U₀)
variable (φ₀ : U₀ ⟶ X₀)

/- Definition 83.4.1 (3): if `B = S` and `C` is the category of schemes over `S`, a
categorical quotient in `C` is a categorical quotient in schemes. -/
@[stacks 048J] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P₀
    AlgebraicGeometry.AlgebraicSpace.PreRelation.isScheme φ₀ : Prop)
