module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import StacksCheckRecall

@[expose] public section

/-!
Compatibility entry for Definition 17.12.1. The reusable owners are
`SheafOfModules.IsCoherent` and `AlgebraicGeometry.RingedSpace.Coh` in
`ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent`.
-/

open AlgebraicGeometry

universe u

variable {X : RingedSpace.{u}} (F : X.Modules)

/- Definition 17.12.1 (01BV): coherence of a module sheaf on a ringed space is the open-site
specialization of `SheafOfModules.IsCoherent`. -/
@[stacks 01BV]
#check (F.IsCoherent : Prop)

/- The associated category of coherent `𝒪_X`-modules is the full subcategory cut out by that
property. -/
#check RingedSpace.Coh X
