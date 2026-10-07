module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
import StacksCheckRecall

/-!
# Definition 18.13.1 compatibility entry point

The direct and inverse image functors for modules on ringed sites are owned by
the neutral `ReasLib.AlgebraicGeometry.RingedSite.Module` leaves.
-/

@[expose] public section

open CategoryTheory
noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (f : X.Hom Y)

/- Definition 18.13.1 (1): direct image regards the ordinary pushforward as a module over the
target structure sheaf via the structure-sheaf map of `f`. -/
@[stacks 03D6 "(1)"]
#check (f.modulePushforward :
  ModuleCat.{z} X ⥤ ModuleCat.{z} Y)

variable [f.modulePushforward.IsRightAdjoint]

/- Definition 18.13.1 (2): inverse image is extension of scalars along the inverse-image form of
the structure-sheaf map. -/
@[stacks 03D6 "(2)"]
#check (f.modulePullback :
  ModuleCat.{z} Y ⥤ ModuleCat.{z} X)

end RingedSite.Hom
