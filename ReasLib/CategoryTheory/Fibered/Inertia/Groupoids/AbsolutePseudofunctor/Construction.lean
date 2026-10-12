/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure.Object
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred inertia pseudofunctor construction

The universe-changing strict lift of neutral absolute inertia through the
groupoid-fibration owner, together with its ordinary pseudofunctor view.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable (C) in
/-- Based inertia preserves the object property selecting groupoid-fibred categories. -/
theorem map_mem
    (X : BasedCategory.{vS, w} C)
    (hX : BasedCategory.isFiberedInGroupoids C X) :
    BasedCategory.isFiberedInGroupoids C
      ((BasedCategory.Inertia.strictPseudofunctor C).obj X) := sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Absolute inertia as the canonical universe-changing strict pseudofunctor on categories
fibred in groupoids. It is the full-subbicategory lift of neutral based inertia, so its actions
on `1`- and `2`-cells are inherited rather than reconstructed. -/
@[stacks 04Z4 "strict pseudofunctorial groupoid-fibred inertia"]
def strictPseudofunctor :
    StrictPseudofunctor
      (FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
      (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :=
  ObjectProperty.FullSubbicategory.map
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)

variable (C) in
/-- The ordinary pseudofunctor view of groupoid-fibred inertia. -/
@[stacks 04Z4 "pseudofunctorial groupoid-fibred inertia"]
abbrev pseudofunctor :
    Pseudofunctor
      (FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
      (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :=
  (strictPseudofunctor C).toPseudofunctor

/- Axiom audit: the non-Prop object, `1`-cell, and `2`-cell actions of
`strictPseudofunctor` are inherited from `BasedCategory.Inertia.strictPseudofunctor`.
`#print axioms` reports `sorryAx` only through the Prop-valued object-membership witness and
inherited law/coherence fields. -/

end Inertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
