/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of localization lower shriek at a point

The stalk of localization lower shriek decomposes over the elements of the
point fiber at the localization object.  The coefficient-general coproduct
statement is primary; the Type-valued sigma statement is its source-facing
specialization.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w a b

namespace CategoryTheory.GrothendieckTopology.Point.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable {A : Type a} [Category.{b} A] [HasColimitsOfSize.{w, w} A]

/-- The fiber at `p` of localization lower shriek is isomorphic to the coproduct of the fibers at
the localized points indexed by `p.fiber.obj U`. -/
@[stacks 04H4 "coefficient-general", stacks 0710 "underlying-sheaf owner"]
theorem lowerShriekFiber_isomorphic_coproduct
    {U : C} (p : Point.{w} J) (G : Sheaf (J.over U) A)
    [((Over.forget U).sheafPushforwardContinuous A (J.over U) J).IsRightAdjoint] :
    IsIsomorphic
      (p.sheafFiber.obj (((Over.forget U).sheafPullback A (J.over U) J).obj G))
      (∐ (fun (x : p.fiber.obj U) ↦ (p.over x).sheafFiber.obj G)) := sorry

/-- The Type-valued form of the lower-shriek fiber decomposition, expressed as the sigma type
whose summands are the fibers at the localized points. -/
@[stacks 04H4]
theorem lowerShriekFiber_isomorphic_sigma
    {U : C} (p : Point.{w} J) (G : Sheaf (J.over U) (Type w))
    [((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).IsRightAdjoint] :
    IsIsomorphic
      (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj G))
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj G) := sorry

end CategoryTheory.GrothendieckTopology.Point.Localization
