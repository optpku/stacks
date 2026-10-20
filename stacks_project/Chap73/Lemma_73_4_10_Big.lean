/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
