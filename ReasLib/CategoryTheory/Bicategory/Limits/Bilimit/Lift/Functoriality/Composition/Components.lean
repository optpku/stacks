/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Components of composition coherence for universal bilimit lifts

The canonical presentation of two successive universal lifts can be evaluated at every
vertex of an arbitrary indexing bicategory. Its component and the endpoint chosen-lift
component give the complete pointwise description of `PseudoCone.lift.comp.iso`.

This is the shape-independent composition API underlying projection formulas for
concrete bilimits.
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

/-- At a diagram vertex, the represented forward composition coherence is the canonical
composite presentation followed by the inverse endpoint chosen-lift comparison. -/
@[simp]
theorem lift.comp.iso.map_hom_app
    (R S T : PseudoCone F) [S.IsBilimit] [T.IsBilimit]
    (j : J) :
    ((T.comparison R.pt).map
        (lift.comp.iso R S T).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp (lift.comp.comparisonIso R S T) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso R T) j).inv := sorry

/-- At a diagram vertex, the represented inverse composition coherence is the endpoint
chosen-lift comparison followed by the inverse canonical composite presentation. -/
@[simp]
theorem lift.comp.iso.map_inv_app
    (R S T : PseudoCone F) [S.IsBilimit] [T.IsBilimit]
    (j : J) :
    ((T.comparison R.pt).map
        (lift.comp.iso R S T).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso R T) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp (lift.comp.comparisonIso R S T) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no data. Its two theorems expose the vertexwise forward and inverse
formulas already specified by `lift.comp.iso.map_hom`, `lift.comp.iso.map_inv`, and
`Pseudofunctor.StrongTrans.isoApp`. -/

end Bicategory.PseudoCone

end CategoryTheory
