module

public import stacks_project.Chap66.Definition_66_19_2_EtaleNeighborhood
import StacksCheckRecall

/- Definition 66.19.2 (1): an étale neighborhood of a geometric point `xbar` of an algebraic
space `X` over a scheme `S` is a commutative triangle `φ : U ⟶ X` of algebraic spaces over `S`
with `φ` étale and a lift of `xbar` to `U`. -/
@[stacks 04JV] #check AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/- Definition 66.19.2 (2): a morphism of étale neighborhoods `(U, ubar) ⟶ (U', ubar')` is an
`X`-morphism `h : U ⟶ U'` such that `ubar' = h ∘ ubar`. -/
@[stacks 04JV] #check AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Hom
