module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 68.11.5 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x` be a point of `X`. An elementary étale neighbourhood is an étale morphism
`(U, u) ⟶ (X, x)` where `U` is a scheme, `u` is a point of `U` mapping to `x`, and
the morphism `Spec(κ(u)) ⟶ X` is a monomorphism. -/
@[stacks 0BGU] #check (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), Type (u + 1))

/- Definition 68.11.5 (2): A morphism of elementary étale neighbourhoods
`(U, u) ⟶ (U', u')` is a morphism `U ⟶ U'` over `X` mapping `u` to `u'`. -/
@[stacks 0BGU] #check (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary.Hom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {x : AlgebraicGeometry.AlgebraicSpace.Points X}
    (U V : AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary X x), Type u)
