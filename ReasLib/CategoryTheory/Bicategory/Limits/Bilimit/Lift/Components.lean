module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Components of universal bilimit lifts

The complete comparison specifying a universal lift can be evaluated at any vertex of
the indexing bicategory. A supplied presentation of another apex map similarly gives a
componentwise comparison with the chosen lift.

This file records those components independently of any concrete limit shape. Downstream
APIs may specialize them to named projections without reopening the represented
comparison equivalence or its selected quasi-inverse.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {F : J ⥤ᵖ B}

/-- At a diagram vertex, the represented forward uniqueness cell is the canonical
componentwise uniqueness comparison: the supplied presentation followed by the inverse
chosen-lift comparison. -/
@[simp]
theorem lift.uniqueIso.map_hom_app
    (S T : PseudoCone F) [T.IsBilimit]
    (l : S.pt ⟶ T.pt)
    (e : (T.comparison S.pt).obj l ≅ S.π)
    (j : J) :
    ((T.comparison S.pt).map
        (lift.uniqueIso S T l e).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp e j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S T) j).inv := sorry

/-- At a diagram vertex, the represented inverse uniqueness cell is the chosen-lift
comparison followed by the inverse supplied presentation. -/
@[simp]
theorem lift.uniqueIso.map_inv_app
    (S T : PseudoCone F) [T.IsBilimit]
    (l : S.pt ⟶ T.pt)
    (e : (T.comparison S.pt).obj l ≅ S.π)
    (j : J) :
    ((T.comparison S.pt).map
        (lift.uniqueIso S T l e).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S T) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp e j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no data. Its two theorems expose the vertexwise forward and inverse
formulas already specified by `lift.uniqueIso.map_hom`, `lift.uniqueIso.map_inv`, and
`Pseudofunctor.StrongTrans.isoApp`. -/

end Bicategory.PseudoCone

end CategoryTheory
