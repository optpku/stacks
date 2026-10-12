/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen lifts from an explicit lifting property

Mathlib exposes a diagonal lift from a `CommSq.HasLift` instance. This leaf instead starts from
an explicit term `h : HasLiftingProperty i p`, chooses the full `CommSq.LiftStruct`, and keeps
the choice available without installing a local instance.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A B X Y : C} {i : A ⟶ B} {p : X ⟶ Y}
variable {f : A ⟶ X} {g : B ⟶ Y}

attribute [simp] CommSq.LiftStruct.fac_left CommSq.LiftStruct.fac_right

namespace HasLiftingProperty

/-- Choose the full lifting structure for a commutative square from an explicit lifting-property
witness. Unlike `CommSq.lift`, this construction does not require a `CommSq.HasLift` instance. -/
@[stacks 08NL "chosen lifting structure"]
noncomputable def liftStruct (h : HasLiftingProperty i p) (sq : CommSq f i p g) :
    sq.LiftStruct :=
  (h.sq_hasLift sq).exists_lift.some

/-- The diagonal morphism underlying the lifting structure chosen from an explicit
lifting-property witness. -/
@[stacks 08NL "chosen diagonal lift"]
noncomputable def lift (h : HasLiftingProperty i p) (sq : CommSq f i p g) : B ⟶ X :=
  (h.liftStruct sq).l

namespace lift

/-- The chosen diagonal lift factors the top map through the left map of the square. -/
@[reassoc (attr := simp), stacks 08NL "left factorization of the chosen lift"]
theorem fac_left (h : HasLiftingProperty i p) (sq : CommSq f i p g) :
    i ≫ h.lift sq = f := sorry

/-- The chosen diagonal lift factors the bottom map through the right map of the square. -/
@[reassoc (attr := simp), stacks 08NL "right factorization of the chosen lift"]
theorem fac_right (h : HasLiftingProperty i p) (sq : CommSq f i p g) :
    h.lift sq ≫ p = g := sorry

end lift

end HasLiftingProperty

end CategoryTheory
