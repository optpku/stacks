/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Closure.Projection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred object closure

This leaf owns the object-property witness used to restrict neutral inertia
to the full subbicategory of categories fibred in sets.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace BasedCategory.isFiberedInSets

variable {C : Type u} [Category.{v} C]

/-- Neutral based inertia preserves the strict object property of being fibred in sets. This is
the direct objectwise closure input for the full-subbicategory inertia pseudofunctor. -/
@[stacks 04Z4 "set-fibred inertia closure"]
theorem inertia
    {X : BasedCategory.{vS, uS} C}
    (hX : BasedCategory.isFiberedInSets C X) :
    BasedCategory.isFiberedInSets C (BasedCategory.inertia X) := sorry

end BasedCategory.isFiberedInSets

end CategoryTheory
