module

public import Mathlib.Order.Directed

@[expose] public section

universe u

namespace Order

/-- A preorder is nonempty and directed exactly when it is nonempty and every pair of
elements has a common upper bound. -/
theorem nonempty_isDirectedOrder_iff (I : Type u) [Preorder I] :
    (Nonempty I ∧ IsDirectedOrder I) ↔
      (Nonempty I ∧ ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k) := sorry

end Order
