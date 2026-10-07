module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Comparison.Left

/-!
# Source-side computations for a chosen pseudoinverse

This file exposes the components and modification data of the source-side
comparison equivalence.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable (F : B ⥤ᵖ C) [F.IsBiequivalence]

namespace ChosenInverse

/-- The forward morphism of the source-side component equivalence is
`leftApp`. -/
@[simp]
theorem leftAppEquivalence.hom (X : B) :
    (leftAppEquivalence F X).hom = leftApp F X := sorry

/-- The inverse morphism of the source-side component equivalence is
`leftInvApp`. -/
@[simp]
theorem leftAppEquivalence.inv (X : B) :
    (leftAppEquivalence F X).inv = leftInvApp F X := sorry

/-- The unit of the source-side component equivalence is the canonical
adjointification of `leftUnitIso`. -/
@[simp]
theorem leftAppEquivalence.unit (X : B) :
    (leftAppEquivalence F X).unit =
      Bicategory.Equivalence.adjointifyUnit
        (leftUnitIso F X) (leftCounitIso F X) := sorry

/-- The counit of the source-side component equivalence is
`leftCounitIso`. -/
@[simp]
theorem leftAppEquivalence.counit (X : B) :
    (leftAppEquivalence F X).counit = leftCounitIso F X := sorry

/-- The component of the source-side strong comparison is the selected local
preimage of the chosen object-equivalence morphism. -/
@[simp]
theorem leftStrongTrans.app (X : B) :
    (leftStrongTrans F).app X = leftApp F X := sorry

/-- The naturality isomorphism of the source-side strong comparison is the
explicit locally lifted isomorphism. -/
@[simp]
theorem leftStrongTrans.naturality {X Y : B} (f : X ⟶ Y) :
    (leftStrongTrans F).naturality f = leftNaturalityIso F f := sorry

/-- The forward strong transformation of the source-side pseudofunctor
equivalence is the explicit source-side comparison. -/
@[simp]
theorem leftEquivalence.hom :
    (leftEquivalence F).hom = leftStrongTrans F := sorry

/-- The naturality isomorphism of the inverse source-side comparison is the
canonical mate of the forward naturality isomorphism. -/
@[simp]
theorem leftEquivalence.inv.naturality {X Y : B} (f : X ⟶ Y) :
    (leftEquivalence F).inv.naturality f =
      StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (leftPointwise F) f := sorry

/-- The forward component of the source-side pseudofunctor equivalence is
`leftApp`. -/
@[simp]
theorem leftEquivalence.hom.app (X : B) :
    (leftEquivalence F).hom.app X = leftApp F X := sorry

/-- The inverse component of the source-side pseudofunctor equivalence is
`leftInvApp`. -/
@[simp]
theorem leftEquivalence.inv.app (X : B) :
    (leftEquivalence F).inv.app X = leftInvApp F X := sorry

/-- The forward unit modification of the source-side equivalence evaluates to
the unit of `leftAppEquivalence`. -/
@[simp]
theorem leftEquivalence.unit.hom.app (X : B) :
    (leftEquivalence F).unit.hom.as.app X =
      (leftAppEquivalence F X).unit.hom := sorry

/-- The inverse unit modification of the source-side equivalence evaluates to
the inverse unit of `leftAppEquivalence`. -/
@[simp]
theorem leftEquivalence.unit.inv.app (X : B) :
    (leftEquivalence F).unit.inv.as.app X =
      (leftAppEquivalence F X).unit.inv := sorry

/-- The forward counit modification of the source-side equivalence evaluates
to the counit of `leftAppEquivalence`. -/
@[simp]
theorem leftEquivalence.counit.hom.app (X : B) :
    (leftEquivalence F).counit.hom.as.app X =
      (leftAppEquivalence F X).counit.hom := sorry

/-- The inverse counit modification of the source-side equivalence evaluates
to the inverse counit of `leftAppEquivalence`. -/
@[simp]
theorem leftEquivalence.counit.inv.app (X : B) :
    (leftEquivalence F).counit.inv.as.app X =
      (leftAppEquivalence F X).counit.inv := sorry

end ChosenInverse

end CategoryTheory.Pseudofunctor
