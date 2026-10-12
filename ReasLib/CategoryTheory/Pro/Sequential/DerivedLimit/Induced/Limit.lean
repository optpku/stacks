/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.Limit
public import ReasLib.CategoryTheory.Pro.Sequential.Quotient

/-!
# Inverse-limit maps induced by sequential pro-morphisms

The representative-level inverse-limit construction descends to common-refinement classes of
sequential presentations.  The computation, identity, and composition API below avoids any
choice of a representative and compares to actual pro-morphisms through `quotientToHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}
variable [HasLimitsOfShape ℕᵒᵖ C]

namespace Quotient

/-- The inverse-limit map induced by a common-refinement class of sequential representatives. -/
noncomputable def limitMap
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y)) :
    limit X ⟶ limit Y :=
  _root_.Quotient.lift Pro.SequentialHom.limitMap
    (fun _ _ h ↦ limitMap_eq_of_equivalent h) η

/-- Computing the induced inverse-limit map on the class of a representative recovers its
representative-level map. -/
@[simp]
theorem limitMap_mk (r : Pro.SequentialHom X Y) :
    limitMap (_root_.Quotient.mk (setoid (X := X) (Y := Y)) r) =
      r.limitMap := sorry

/-- The identity class induces the identity map on inverse limits. -/
@[simp]
theorem limitMap_id (X : SequentialInverseSystem C) :
    limitMap (id X) = 𝟙 (limit X) := sorry

/-- Composition of common-refinement classes induces composition of their inverse-limit maps. -/
@[simp]
theorem limitMap_comp {Z : SequentialInverseSystem C}
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    (θ : Pro.SequentialHom.Quotient (X := Y) (Y := Z)) :
    limitMap (comp η θ) = limitMap η ≫ limitMap θ := sorry

/-- A sequential morphism class whose associated pro-morphism is invertible induces an
isomorphism on inverse limits. -/
theorem limitMap_isIso
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    [IsIso (quotientToHom η)] : IsIso (limitMap η) := sorry

end Quotient

end CategoryTheory.Pro.SequentialHom
