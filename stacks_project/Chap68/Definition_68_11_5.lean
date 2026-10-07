module

public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Definition 68.11.5 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x` be a point of `X`. An elementary étale neighbourhood is an étale morphism
`(U, u) ⟶ (X, x)` where `U` is a scheme, `u` is a point of `U` mapping to `x`, and
the morphism `Spec(κ(u)) ⟶ X` is a monomorphism. -/
@[stacks 0BGU] #check EtaleNeighborhood.Elementary

/- Definition 68.11.5 (2): A morphism of elementary étale neighbourhoods
`(U, u) ⟶ (U', u')` is a morphism `U ⟶ U'` over `X` mapping `u` to `u'`. -/
@[stacks 0BGU] #check EtaleNeighborhood.Elementary.Hom
