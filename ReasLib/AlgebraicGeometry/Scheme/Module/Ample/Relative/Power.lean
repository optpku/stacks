module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Power

/-!
# Relative ampleness of tensor powers

This file relates relative ampleness of an invertible module to relative ampleness of its
positive tensor powers.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An invertible module is relatively ample over a scheme morphism if and only if any positive
tensor power is relatively ample over the same morphism. -/
theorem relativelyAmple_iff_tensorPow_relativelyAmple
    {X S : Scheme.{u}} {f : X ⟶ S}
    (L : X.Modules) [hL : Scheme.Modules.Invertible L] (n : ℕ) (hn : 0 < n) :
    RelativelyAmple f L ↔
      RelativelyAmple f (RingedSpace.TensorPower.sheaf L n) := sorry

end AlgebraicGeometry
