module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero maps on exterior powers

The degree-zero exterior power is exceptional, while every positive exterior
power of a zero map is zero.  This fact is independent of finite generation or
coordinate choices and is therefore kept at the general exterior-power layer.
-/

@[expose] public section

universe u v w

namespace exteriorPower

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A positive exterior power sends the zero linear map to the zero map. -/
@[stacks 00MV "positive exterior power of a zero map"]
theorem map_zero_of_pos {r : ℕ} (hr : 0 < r) :
    map r (0 : M →ₗ[R] N) = 0 := sorry

end exteriorPower
