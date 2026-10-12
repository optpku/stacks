/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Small.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Size of endofunctor categories

Universe-size obstructions for categories of endofunctors on large categories of types.
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- The category of endofunctors of Type u is not u-small. -/
@[stacks 02C2]
theorem not_small_type_endofunctor :
    ¬ Small.{u} (Type u ⥤ Type u) := sorry

end CategoryTheory
