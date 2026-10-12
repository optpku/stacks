/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure.Projection
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred object closure

This leaf owns the object-property witness used to restrict neutral inertia
to the full subbicategory of categories fibred in setoids.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace isFiberedInSetoids

/-- Neutral based inertia preserves the object property of being fibred in setoids. This is the
objectwise closure input for restricting the ambient inertia pseudofunctor to the canonical full
subbicategory. -/
@[stacks 04Z4 "setoid-fibred inertia closure"]
theorem inertia
    {X : BasedCategory.{vS, uS} C}
    (hX : BasedCategory.isFiberedInSetoids C X) :
    BasedCategory.isFiberedInSetoids C (BasedCategory.inertia X) := sorry

end isFiberedInSetoids

end BasedCategory

end CategoryTheory
