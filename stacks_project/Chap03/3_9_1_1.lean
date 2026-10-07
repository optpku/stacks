module

public import stacks_project.Chap03.«3_9_1_1_Bound»

@[expose] public section

noncomputable section

universe u

open scoped Cardinal
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- 3.9.1.1: the Stacks bound of a cardinal `κ` is `max (κ ^ ℵ₀) (Order.succ κ)`. -/
@[stacks 046U]
theorem bound_eq (κ : Cardinal.{u}) : bound κ = max (κ ^ ℵ₀) (Order.succ κ) := sorry

end AlgebraicGeometry.Scheme
