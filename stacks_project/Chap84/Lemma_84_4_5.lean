module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ProperStalk

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 84.4.5: For a proper morphism of algebraic spaces, the canonical map
from the geometric stalk of the pushforward to sections on the geometric fibre
is bijective. -/
@[stacks 0DG1] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePushforwardStalk_bijective_of_proper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Proper f]
      (xbar : GeometricPoint X)
      (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))),
      Function.Bijective
        (smallEtalePushforwardStalkToGeometricFiberSections f xbar F))
