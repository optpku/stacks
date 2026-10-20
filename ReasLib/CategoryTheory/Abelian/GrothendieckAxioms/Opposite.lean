module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Countable.Opposite

/-!
# Countable AB4 and opposite categories

Exact countable coproducts in an opposite category are the same condition as exact countable
products in the original category.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasCountableProducts C]

/-- Countable `AB4` on the opposite category is equivalent to countable `AB4*` on the original
category. -/
@[stacks 0AMH]
theorem countableAB4_op_iff_countableAB4Star :
    CountableAB4 Cᵒᵖ ↔ CountableAB4Star C := sorry

/-- Failure of exact countable products is transported to failure of exact countable coproducts
in the opposite category. -/
theorem not_countableAB4_op_iff_not_countableAB4Star :
    (¬ CountableAB4 Cᵒᵖ) ↔ ¬ CountableAB4Star C := sorry

end CategoryTheory
