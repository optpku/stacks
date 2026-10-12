/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite bounds in directed preorders

This leaf isolates the finite combinatorics of directed preorders.  It is
independent of a particular direct-limit construction, so algebraic and
categorical consumers can import it without inheriting unrelated support.
-/

@[expose] public section

universe u

namespace Finset

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- A finite family of indices in a nonempty directed preorder has a common
upper bound. -/
@[stacks 00QV "finite directed upper bound"]
theorem exists_upper_bound_of_directed (s : Finset I) :
    ∃ i : I, ∀ j ∈ s, j ≤ i := sorry

end Finset
