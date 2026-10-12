/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Comparison.Right

/-!
# Target-side computations for a chosen pseudoinverse

This file exposes the components and modification data of the target-side
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

/-- The component of the target-side strong comparison is the chosen object
equivalence morphism. -/
@[simp]
theorem rightStrongTrans.app (X : C) :
    (rightStrongTrans F).app X = (objPreimage.equivalence F X).hom := sorry

/-- The naturality isomorphism of the target-side strong comparison is the
explicit counit-cancellation isomorphism. -/
@[simp]
theorem rightStrongTrans.naturality {X Y : C} (f : X ⟶ Y) :
    (rightStrongTrans F).naturality f = rightNaturalityIso F f := sorry

/-- The forward strong transformation of the target-side pseudofunctor
equivalence is the explicit target-side comparison. -/
@[simp]
theorem rightEquivalence.hom :
    (rightEquivalence F).hom = rightStrongTrans F := sorry

/-- The naturality isomorphism of the inverse target-side comparison is the
canonical mate of the forward naturality isomorphism. -/
@[simp]
theorem rightEquivalence.inv.naturality {X Y : C} (f : X ⟶ Y) :
    (rightEquivalence F).inv.naturality f =
      StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (rightPointwise F) f := sorry

/-- The forward component of the target-side pseudofunctor equivalence is the
chosen object-equivalence morphism. -/
@[simp]
theorem rightEquivalence.hom.app (X : C) :
    (rightEquivalence F).hom.app X = (objPreimage.equivalence F X).hom := sorry

/-- The inverse component of the target-side pseudofunctor equivalence is the
chosen object-equivalence inverse. -/
@[simp]
theorem rightEquivalence.inv.app (X : C) :
    (rightEquivalence F).inv.app X = (objPreimage.equivalence F X).inv := sorry

/-- The forward unit modification of the target-side equivalence evaluates to
the chosen object-equivalence unit. -/
@[simp]
theorem rightEquivalence.unit.hom.app (X : C) :
    (rightEquivalence F).unit.hom.as.app X =
      (objPreimage.equivalence F X).unit.hom := sorry

/-- The inverse unit modification of the target-side equivalence evaluates to
the inverse chosen object-equivalence unit. -/
@[simp]
theorem rightEquivalence.unit.inv.app (X : C) :
    (rightEquivalence F).unit.inv.as.app X =
      (objPreimage.equivalence F X).unit.inv := sorry

/-- The forward counit modification of the target-side equivalence evaluates
to the chosen object-equivalence counit. -/
@[simp]
theorem rightEquivalence.counit.hom.app (X : C) :
    (rightEquivalence F).counit.hom.as.app X =
      (objPreimage.equivalence F X).counit.hom := sorry

/-- The inverse counit modification of the target-side equivalence evaluates
to the inverse chosen object-equivalence counit. -/
@[simp]
theorem rightEquivalence.counit.inv.app (X : C) :
    (rightEquivalence F).counit.inv.as.app X =
      (objPreimage.equivalence F X).counit.inv := sorry

end ChosenInverse

end CategoryTheory.Pseudofunctor
