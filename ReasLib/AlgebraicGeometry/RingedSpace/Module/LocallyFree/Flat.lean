module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree

/-!
# Flatness of locally free module sheaves

This leaf installs the canonical implication from local freeness to stalkwise flatness without
making the base flatness owner depend on the local-freeness hierarchy.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.IsLocallyFree

variable {X : RingedSpace.{u}}

/-- A locally free module sheaf on a ringed space is flat. -/
@[stacks 05ND "locally free module sheaves are flat", instance]
theorem isFlat (ℱ : X.Modules) [ℱ.IsLocallyFree] : ℱ.IsFlat := sorry

end SheafOfModules.IsLocallyFree
