module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Pullback.Kernel
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback and kernel ideals on locally ringed spaces
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IdealSubobject

/-- The pulled-back ideal map vanishes exactly when the ideal lies in the kernel ideal of the
locally ringed-space morphism. -/
@[stacks 01HP "locally ringed-space ideal-kernel criterion"]
theorem pullback_eq_zero_iff_le_kernel
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullbackMap f = 0 ↔ I ≤ Hom.kernelIdealSubobject f := sorry

/-- The inverse-image ideal is bottom exactly when the ideal lies in the kernel ideal of the
locally ringed-space morphism. -/
@[stacks 01HP "locally ringed-space inverse-image ideal bottom criterion"]
theorem pullback_eq_bot_iff_le_kernel
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullback f = ⊥ ↔ I ≤ Hom.kernelIdealSubobject f := sorry

end AlgebraicGeometry.LocallyRingedSpace.IdealSubobject
