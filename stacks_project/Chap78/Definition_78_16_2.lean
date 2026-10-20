module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/- Definition 78.16.2: the group algebraic space `j⁻¹(Δ_{U/B}) ⟶ U` is called
the stabilizer of the groupoid in algebraic spaces `(U, R, s, t, c)` over `B`. -/
@[stacks 0448] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer G : Grp (Over G.U))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer_X G :
  G.stabilizer.X = G.toPreRelation.stabilizer)
