module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Topos
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Definition 66.18.7: let `S` be a scheme and let `X` be an algebraic space over `S`.
The étale topos of `X`, or more precisely the small étale topos of `X`, is the category
`Sheaf (SmallEtale.topology X) (Type w)` of sheaves of sets on the small étale site of `X`. -/
@[stacks 04JT] #check (AlgebraicGeometry.AlgebraicSpace.SmallEtale.topos.{u, w} X :
  Type (max (u + 1) (w + 1)))
