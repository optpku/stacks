module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
import StacksCheckRecall

@[expose]
public section

universe u

/- Definition 67.14.4 (1): the scheme-theoretic intersection of closed subspaces
of an algebraic space `X` corresponding to quasi-coherent ideal sheaves `I` and
`J` is the closed subspace of `X` cut out by `I ⊔ J`. -/
@[stacks 0CYZ] #check (AlgebraicGeometry.AlgebraicSpace.schemeTheoreticIntersection :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (I J : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X),
    [AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent I] →
    [AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent J] →
    AlgebraicGeometry.AlgebraicSpace S)

#check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticIntersection_eq_subscheme_sup

/- Definition 67.14.4 (2): the scheme-theoretic union of closed subspaces of an
algebraic space `X` corresponding to quasi-coherent ideal sheaves `I` and `J` is
the closed subspace of `X` cut out by `I ⊓ J`. -/
@[stacks 0CYZ] #check (AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (I J : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X),
    [AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent I] →
    [AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent J] →
    AlgebraicGeometry.AlgebraicSpace S)

#check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion_eq_subscheme_inf
