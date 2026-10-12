/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Topos
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/- Situation 21.38.1 (08P8): a fibred category over a ringed site carries the topology and
structure sheaf inherited along its projection, with the canonical projection morphism of
ringed topoi. -/
@[stacks 08P8 "fibred category over the base"]
#check @FiberedCategoryOver

@[stacks 08P8 "total category"]
#check @FiberedCategoryOver.total

@[stacks 08P8 "projection functor"]
#check @FiberedCategoryOver.p

@[stacks 08P8 "inherited topology"]
#check @Functor.inheritedTopology

@[stacks 08P8 "inherited morphism of topoi"]
#check @Functor.inheritedTopology.morphismOfTopoi

@[stacks 08P8 "inherited ringed topos"]
#check @Functor.inheritedRingedTopos

@[stacks 08P8 "projection morphism of inherited ringed topoi"]
#check @Functor.inheritedProjectionToposHom

@[stacks 08P8 "projection topos morphism"]
#check @Functor.inheritedProjectionToposHom_toTopos

@[stacks 08P8 "projection structure-sheaf map"]
#check @Functor.inheritedProjectionToposHom_structureMap

-- When the projection is also representably flat, the stronger site presentation remains
-- available as a companion API.
#check @Functor.inheritedRingedSite
#check @Functor.inheritedProjectionRingedSiteHom

end CategoryTheory
