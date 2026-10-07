module

public import stacks_project.Chap83.Definition_83_6_1_Coarse
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
variable (φ : U ⟶ X)

/- Definition 83.6.1 (1): a morphism `φ : U ⟶ X` of algebraic spaces over `B` is a
coarse quotient of a pre-relation `P` when it is a categorical quotient and an orbit
space. -/
@[stacks 04A2] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCoarseQuotient P φ : Prop)

variable {U₀ X₀ : Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S)))}
variable (P₀ : AlgebraicGeometry.AlgebraicSpace.PreRelation U₀)
variable (φ₀ : U₀ ⟶ X₀)

/- Definition 83.6.1 (2): if `B = S` and `U`, `R`, `X` are schemes, a morphism of schemes
`φ : U ⟶ X` is a coarse quotient in schemes when it is a categorical quotient in schemes
and an orbit space. -/
@[stacks 04A2] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCoarseQuotientInSchemes P₀ φ₀ : Prop)
