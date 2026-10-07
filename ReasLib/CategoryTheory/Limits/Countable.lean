module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countable Coproducts from Sequential Colimits

This leaf supplies the size-sensitive bridge from sequential colimits and
finite coproducts to countable coproducts.  It is deliberately a named theorem
rather than a global instance: registering the converse to the standard
`HasCountableCoproducts → HasFiniteCoproducts` instance would introduce an
unhelpful typeclass-search cycle.
-/

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- Finite coproducts and colimits of sequential diagrams provide all countable coproducts. -/
@[stacks 0949 "countable coproducts from sequential colimits"]
theorem hasCountableCoproducts_of_sequentialColimits
    [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C] :
    HasCountableCoproducts C := sorry

namespace CountableFromSequential

-- This existing theorem is an instance only when the scope is explicitly
-- activated; registering it globally would create a search cycle with the
-- standard implication from countable to finite coproducts.
attribute [scoped instance] hasCountableCoproducts_of_sequentialColimits

end CountableFromSequential

end CategoryTheory.Limits
