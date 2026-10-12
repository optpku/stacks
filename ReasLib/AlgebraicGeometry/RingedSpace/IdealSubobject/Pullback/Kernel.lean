/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback and kernel ideal subobjects

This interaction leaf owns the vanishing criteria relating inverse-image ideals to kernel ideals.
The pullback construction itself remains independent of kernels.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSubobject

/-- The pulled-back ideal map vanishes exactly when the original ideal lies in the kernel ideal
of the morphism. -/
@[stacks 01HP "ideal-kernel vanishing criterion"]
theorem pullback_eq_zero_iff_le_kernel
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullbackMap f = 0 ↔ I ≤ Hom.kernelIdealSubobject f := sorry

/-- The inverse-image ideal is bottom exactly when the original ideal lies in the kernel ideal
of the morphism. -/
@[stacks 01HP "inverse-image ideal bottom criterion"]
theorem pullback_eq_bot_iff_le_kernel
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullback f = ⊥ ↔ I ≤ Hom.kernelIdealSubobject f := sorry

end AlgebraicGeometry.RingedSpace.IdealSubobject
