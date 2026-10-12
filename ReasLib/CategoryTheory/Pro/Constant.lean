/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Presentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant pro-objects

This module gives the presentation-independent meaning of a pro-system having a specified value:
the corresponding pro-object is isomorphic to a constant pro-object. Presentation-level
Hom-colimit criteria belong in `Pro.Representative`.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe uC vC

namespace CategoryTheory

namespace Pro

variable {C : Type uC} [Category.{vC} C]

/-- A pro-object has constant value `X` when it is isomorphic to the constant pro-object on `X`.
This is the presentation-independent form of the value notion used in Lemma 13.42.2 (0G3A). -/
@[stacks 0G3A]
def IsConstant (P : Pro C) (X : C) : Prop :=
  Nonempty (P ≅ Pro.yoneda.obj X)

namespace IsConstant

variable {P Q : Pro C} {X Y : C}

/-- Constantness transports along an isomorphism of pro-objects. -/
theorem of_iso (h : IsConstant P X) (e : P ≅ Q) : IsConstant Q X := sorry

/-- Constantness transports along an isomorphism of value objects. -/
theorem of_value_iso (h : IsConstant P X) (e : X ≅ Y) : IsConstant P Y := sorry

/-- Any two constant values of the same pro-object are isomorphic. -/
theorem nonempty_value_iso (hX : IsConstant P X) (hY : IsConstant P Y) :
    Nonempty (X ≅ Y) := sorry

end IsConstant

end Pro

end CategoryTheory
