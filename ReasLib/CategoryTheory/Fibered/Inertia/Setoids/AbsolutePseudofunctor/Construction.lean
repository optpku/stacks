/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure.Object
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred inertia pseudofunctor construction

The universe-changing strict lift of neutral absolute inertia through the
setoid-fibration owner, together with its ordinary pseudofunctor view.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable (C) in
/-- Based inertia preserves the object property selecting setoid-fibred categories. -/
theorem map_mem
    (X : BasedCategory.{vS, w} C)
    (hX : BasedCategory.isFiberedInSetoids C X) :
    BasedCategory.isFiberedInSetoids C
      ((BasedCategory.Inertia.strictPseudofunctor C).obj X) := sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Absolute inertia as the canonical universe-changing strict pseudofunctor on categories
fibred in setoids. It is obtained by lifting neutral based inertia through the existing full
subbicategory owner, so the `1`- and `2`-cell data are inherited unchanged. -/
@[stacks 04Z4 "strict setoid-fibred absolute inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (FiberedCategoryOver.Setoids.{u, v, w, vS} C)
      (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :=
  ObjectProperty.FullSubbicategory.map
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)

variable (C) in
/-- The ordinary pseudofunctor view of setoid-fibred inertia. -/
@[stacks 04Z4 "setoid-fibred absolute inertia pseudofunctor"]
abbrev pseudofunctor :
    Pseudofunctor
      (FiberedCategoryOver.Setoids.{u, v, w, vS} C)
      (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :=
  (strictPseudofunctor C).toPseudofunctor

/- Axiom audit: the object, `1`-cell, and `2`-cell data of `strictPseudofunctor` are inherited
from `BasedCategory.Inertia.strictPseudofunctor`. Its only additional proof debt is the
Prop-valued setoid-fibration membership of each image object. -/

end Inertia

end FiberedCategoryOver.Setoids

end CategoryTheory
