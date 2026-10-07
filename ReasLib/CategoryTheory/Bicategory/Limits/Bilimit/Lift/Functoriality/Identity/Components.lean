module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Components of identity coherence for universal bilimit lifts

The canonical presentation of the identity apex map can be evaluated at every vertex
of an arbitrary indexing bicategory. Its component and the chosen-lift component give
the complete pointwise description of `PseudoCone.lift.id.iso`.

This is the shape-independent identity API underlying projection formulas for concrete
bilimits.
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

/-- At a diagram vertex, the represented forward identity coherence is the canonical
identity presentation followed by the inverse chosen-lift comparison. -/
@[simp]
theorem lift.id.iso.map_hom_app
    (S : PseudoCone F) [S.IsBilimit] (j : J) :
    ((S.comparison S.pt).map
        (lift.id.iso S).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp (lift.id.comparisonIso S) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S S) j).inv := sorry

/-- At a diagram vertex, the represented inverse identity coherence is the chosen-lift
comparison followed by the inverse canonical identity presentation. -/
@[simp]
theorem lift.id.iso.map_inv_app
    (S : PseudoCone F) [S.IsBilimit] (j : J) :
    ((S.comparison S.pt).map
        (lift.id.iso S).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S S) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp (lift.id.comparisonIso S) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no data. Its two theorems expose the vertexwise forward and inverse
formulas already specified by `lift.id.iso.map_hom`, `lift.id.iso.map_inv`, and
`Pseudofunctor.StrongTrans.isoApp`. -/

end Bicategory.PseudoCone

end CategoryTheory
