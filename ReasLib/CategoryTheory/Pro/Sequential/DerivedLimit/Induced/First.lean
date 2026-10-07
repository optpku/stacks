module

public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.First
public import ReasLib.CategoryTheory.Pro.Sequential.Quotient

/-!
# First derived inverse-limit maps induced by sequential pro-morphisms

The Milnor-cokernel map of a sequential representative descends to its common-refinement class.
Its public API makes no representative choice and exposes the expected identity and composition
computations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

open SequentialInverseSystem.Milnor.ProductCone

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SequentialInverseSystem C}
variable [HasCountableProducts C] [HasCokernels C]

namespace Quotient

/-- The map on neutral canonical Milnor cokernels induced by a common-refinement class of
sequential representatives. -/
noncomputable def firstDerivedLimitMap
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y)) :
    canonicalR1 X ⟶ canonicalR1 Y :=
  _root_.Quotient.lift Pro.SequentialHom.firstDerivedLimitMap
    (fun _ _ h ↦ firstDerivedLimitMap_eq_of_equivalent h) η

/-- Computing the induced first derived-limit map on the class of a representative recovers its
representative-level map. -/
@[simp]
theorem firstDerivedLimitMap_mk (r : Pro.SequentialHom X Y) :
    firstDerivedLimitMap
      (_root_.Quotient.mk (setoid (X := X) (Y := Y)) r) =
        r.firstDerivedLimitMap := sorry

/-- The identity class induces the identity map on the neutral canonical Milnor cokernel. -/
@[simp]
theorem firstDerivedLimitMap_id (X : SequentialInverseSystem C) :
    firstDerivedLimitMap (id X) =
      𝟙 (canonicalR1 X) := sorry

/-- Composition of common-refinement classes induces composition of their maps on
canonical Milnor cokernels. -/
@[simp]
theorem firstDerivedLimitMap_comp {Z : SequentialInverseSystem C}
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    (θ : Pro.SequentialHom.Quotient (X := Y) (Y := Z)) :
    firstDerivedLimitMap (comp η θ) =
      firstDerivedLimitMap η ≫ firstDerivedLimitMap θ := sorry

/-- A sequential morphism class whose associated pro-morphism is invertible induces an
isomorphism on the canonical first derived limit. -/
theorem firstDerivedLimitMap_isIso
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    [IsIso (quotientToHom η)] : IsIso (firstDerivedLimitMap η) := sorry

end Quotient

end CategoryTheory.Pro.SequentialHom
