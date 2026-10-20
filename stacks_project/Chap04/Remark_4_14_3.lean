module

import Mathlib.CategoryTheory.Limits.HasLimits
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe vJ uJ vC uC

variable (J : Type uJ) [Category.{vJ} J]
variable (C : Type uC) [Category.{vC} C]

/-
Remark 4.14.3 is a metamathematical size convention: an indexing category for a limit or colimit
must have a set of objects in the foundational universe fixed by the Stacks Project, rather than
belonging to the proper-class whitelist of Remark 4.2.2.

Lean does not encode that fixed-universe whitelist. A diagram shape is instead an arbitrary
universe-indexed type `J : Type u₁` with `[Category.{v₁} J]`; the universe parameters on
`HasLimitsOfShape J C` and `HasColimitsOfShape J C` record its size. In particular,
`SmallCategory J` is not a translation of this remark: it only identifies the object and morphism
universes of `J`. Likewise, `HasLimitsOfSize.{v₁, u₁} C` and
`HasColimitsOfSize.{v₁, u₁} C` quantify over shapes in specified universes, but no particular
universe bound is supplied by the source item.

Thus this convention introduces no additional Lean declaration. The existing shape-indexed
(co)limit classes below are the canonical APIs that carry the relevant universe information.
-/
@[stacks 002G "universe-indexed shapes for limits and colimits"]
#check (HasLimitsOfShape J C : Prop)

#check (HasColimitsOfShape J C : Prop)

end CategoryTheory.Limits
