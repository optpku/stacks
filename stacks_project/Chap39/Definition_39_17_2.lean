module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer
import StacksCheckRecall

universe u

/- Definition 39.17.2: for a groupoid scheme, the group scheme obtained by pulling the
relation map back along the diagonal is its stabilizer. -/
@[stacks 0236] #check (AlgebraicGeometry.GroupoidScheme.stabilizer :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
    CategoryTheory.Grp (CategoryTheory.Over G.U))

#check (AlgebraicGeometry.GroupoidScheme.stabilizer_X :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
    (AlgebraicGeometry.GroupoidScheme.stabilizer G).X = G.toPreRelation.stabilizer)
