module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

/-!
# Big étale sheaf functors on algebraic spaces

The big étale morphism of topoi is supplied by the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi f :
  MorphismOfTopoiIn (AlgebraicSpace.overEtaleTopology X) (AlgebraicSpace.overEtaleTopology Y))

end AlgebraicGeometry
