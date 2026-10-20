/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Countable
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact Coproducts Indexed by Countable Types

`CountableAB4` is stated in Mathlib for countable types in the small universe.
This leaf supplies the universe-polymorphic transport needed by consumers whose
countable indexing type lives in another universe.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u uI

namespace CategoryTheory

namespace HasExactColimitsOfShape

/-- Stacks 0A5L: exact countable coproducts give exact coproducts indexed by every
countable type, independently of the universe of that type. -/
@[stacks 0A5L]
instance (priority := 100) of_countableAB4
    {C : Type u} [Category.{v} C] [HasCountableCoproducts C] [CountableAB4 C]
    (α : Type uI) [Countable α] :
    HasExactColimitsOfShape (Discrete α) C := sorry

end HasExactColimitsOfShape

namespace Limits.CountableFromSequential

-- Mathlib keeps this canonical construction local to avoid instance diamonds.
-- Activating it only in this scope supplies the finite biproduct input required
-- by `CountableAB4.of_countableAB5` without changing global instance search.
attribute [scoped instance] Abelian.hasFiniteBiproducts

-- Mathlib already owns the exactness implication.  The same opt-in scope
-- activates it together with the chosen finite and countable coproducts.
attribute [scoped instance] CountableAB4.of_countableAB5

end Limits.CountableFromSequential

end CategoryTheory
