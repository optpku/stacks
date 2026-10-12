/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Shift.CommShift
public import ReasLib.CategoryTheory.Localization.Lifting.Computation

/-!
# Shift Structures Along Localization Liftings

This leaf transports a pointwise shift structure from a functor before localization to its
chosen localization lifting.  The representative choice and its temporary essential-surjectivity
instance are confined here; downstream instances depend only on the lifted functor and object.
-/

@[expose] public section

noncomputable section

universe vC vD vA vB uC uD uA uB

open CategoryTheory

namespace CategoryTheory.Localization.Lifting

variable {C : Type uC} {D : Type uD} {A : Type uA} {B : Type uB}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vA} A] [Category.{vB} B]
variable {S : Type*} [AddMonoid S] [HasShift A S] [HasShift B S]
variable {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
variable {F : C ⥤ A ⥤ B} {F' : D ⥤ A ⥤ B}
variable [Localization.Lifting L W F F']

/-- A pointwise shift structure descends along a localization lifting.  The local instance is
the canonical essential surjectivity attached to `L.IsLocalization W`, used only to choose a
source representative of `K`. -/
@[implicit_reducible, stacks 05SE "shift structure along a localization lifting"]
noncomputable def objCommShift (hF : ∀ X : C, (F.obj X).CommShift S) (K : D) :
    (F'.obj K).CommShift S :=
  letI := Localization.essSurj L W
  let X := L.objPreimage K
  letI := hF X
  let e := (Localization.Lifting.iso L W F F').symm.app X ≪≫
    F'.mapIso (L.objObjPreimageIso K)
  Functor.CommShift.ofIso e S

end CategoryTheory.Localization.Lifting
