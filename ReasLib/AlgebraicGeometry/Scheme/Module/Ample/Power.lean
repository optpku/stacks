module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An invertible module on a scheme is ample if and only if any positive tensor power is ample. -/
theorem isAmple_iff_tensorPow_isAmple
    (L : X.Modules) [hL : Invertible L] (n : ℕ) (hn : 0 < n) :
    IsAmple L ↔
      @IsAmple X (RingedSpace.TensorPower.sheaf L n)
        (Invertible.tensorPower_isInvertible hL n) := sorry

/-- Every positive tensor power of an ample invertible module is ample. -/
theorem IsAmple.tensorPow
    {L : X.Modules} [hL : Invertible L] (hA : IsAmple L)
    {n : ℕ} (hn : 0 < n) :
    @IsAmple X (RingedSpace.TensorPower.sheaf L n)
      (Invertible.tensorPower_isInvertible hL n) :=
  (isAmple_iff_tensorPow_isAmple L n hn).1 hA

/-- An invertible module is ample if one of its positive tensor powers is ample. -/
theorem IsAmple.of_tensorPow
    {L : X.Modules} [hL : Invertible L]
    {n : ℕ} (hn : 0 < n)
    (hA : @IsAmple X (RingedSpace.TensorPower.sheaf L n)
      (Invertible.tensorPower_isInvertible hL n)) :
    IsAmple L :=
  (isAmple_iff_tensorPow_isAmple L n hn).2 hA

end AlgebraicGeometry.Scheme.Modules
