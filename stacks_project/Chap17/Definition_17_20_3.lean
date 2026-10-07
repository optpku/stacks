module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
import StacksCheckRecall

/-!
# Definition 17.20.3

Relative flatness is owned in ReasLib by the restricted `f⁻¹𝒪_Y`-module and its
target-stalk model.
-/

@[expose] public section

/- Definition 17.20.3 (1): flatness over the target at one source point. -/
@[stacks 08KT "(1)"]
#check @SheafOfModules.IsFlatOverAt

/- Definition 17.20.3 (2): flatness over the target at every source point. -/
@[stacks 08KT "(2)"]
#check @SheafOfModules.IsFlatOver

/- The global and pointwise formulations are connected by the reusable stalkwise bridge. -/
#check @SheafOfModules.isFlatOver_iff_forall_isFlatOverAt

/- The RingedSpace formulation integrates directly with the generic RingedSite owner. -/
#check @SheafOfModules.isFlatOver_iff_ringedSite
