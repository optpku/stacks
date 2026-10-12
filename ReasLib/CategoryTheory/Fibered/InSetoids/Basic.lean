/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Fibers
public import ReasLib.CategoryTheory.Groupoid.Thin

/-!
# Categories fibred in setoids

The intrinsic projection-level condition is fibredness in groupoids together with faithfulness.
It is equivalently expressed by thinness of every standard fiber.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

/-- A category fibred in setoids over `C` is a category fibred in groupoids whose projection is
faithful. This intrinsic owner is independent of a chosen cleavage or discrete skeleton. -/
@[stacks 04SA]
class IsFibered.InSetoids (p : S ⥤ C) : Prop extends IsFibered.InGroupoids p, p.Faithful

attribute [stacks 04SA "setoid-fibration groupoid field"]
  Functor.IsFibered.InSetoids.toInGroupoids
attribute [stacks 04SA "setoid-fibration faithful field"]
  Functor.IsFibered.InSetoids.toFaithful

namespace IsFibered.InSetoids

/-- Construct the intrinsic setoid-fibration owner from its two mathematical components. -/
theorem of_inGroupoids_faithful
    (p : S ⥤ C) (h_groupoids : IsFibered.InGroupoids p) (h_faithful : p.Faithful) :
    IsFibered.InSetoids p := sorry

/-- The identity functor is canonically fibred in setoids. -/
instance id : IsFibered.InSetoids (Functor.id C) := sorry

/-- Every standard fiber of a category fibred in setoids is thin. -/
instance fiberIsThin (p : S ⥤ C) [IsFibered.InSetoids p] (U : C) :
    Quiver.IsThin (p.Fiber U) := sorry

end IsFibered.InSetoids

/-- The intrinsic owner records exactly fibredness in groupoids and faithfulness of the
projection. -/
theorem IsFibered.InSetoids.iff_inGroupoids_faithful (p : S ⥤ C) :
    IsFibered.InSetoids p ↔ IsFibered.InGroupoids p ∧ p.Faithful := sorry

/-- The intrinsic owner is equivalent to fibredness in groupoids together with thin standard
fibres. -/
theorem IsFibered.InSetoids.iff_inGroupoids_fibersThin (p : S ⥤ C) :
    IsFibered.InSetoids p ↔
      IsFibered.InGroupoids p ∧ ∀ U : C, Quiver.IsThin (p.Fiber U) := sorry

/-- A category fibred in setoids is equivalently a category fibred in groupoids whose every fiber
object has a subsingleton automorphism type. -/
theorem IsFibered.InSetoids.iff_inGroupoids_fibersSubsingletonAut (p : S ⥤ C) :
    IsFibered.InSetoids p ↔
      IsFibered.InGroupoids p ∧ ∀ (U : C) (x : p.Fiber U), Subsingleton (Aut x) := sorry

end Functor

end CategoryTheory
