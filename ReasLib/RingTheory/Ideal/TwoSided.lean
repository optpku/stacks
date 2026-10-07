module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-sided ideals

This leaf records elementary closure facts for the `Ideal.IsTwoSided` predicate. They are
theorems rather than global instances because the relevant ideals are commonly local choices in a
quotient construction.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Semiring R]

/-- The supremum of two two-sided ideals is two-sided. -/
@[stacks 0H7M "supremum of two-sided ideals"]
theorem isTwoSided_sup (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] :
    (I ⊔ J).IsTwoSided := sorry

end Ideal
