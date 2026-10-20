module

public import Mathlib.Order.Interval.Set.InitialSeg

/-!
# The order homomorphism from `Iio` to `Iic`

This file provides the monotone inclusion of a strict lower interval into the
corresponding closed lower interval for an arbitrary preorder.
-/

@[expose] public section

universe u

namespace Set

variable {α : Type u} [Preorder α]

namespace iioToIic

/-- The evident inclusion `Iio a → Iic a` is monotone for any preorder. -/
theorem monotone (a : α) :
    Monotone (fun i : Iio a => (⟨i.1, i.2.le⟩ : Iic a)) := sorry

end iioToIic

/-- The order homomorphism including `Iio a` into `Iic a`. -/
def iioToIic (a : α) : Iio a →o Iic a where
  toFun i := ⟨i.1, i.2.le⟩
  monotone' := iioToIic.monotone a

namespace iioToIic

/-- The `Iio`-to-`Iic` inclusion retains the underlying index. -/
@[simp]
theorem apply (a : α) (i : Iio a) :
    iioToIic a i = ⟨i.1, i.2.le⟩ := sorry

end iioToIic

end Set
