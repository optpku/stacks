/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Lift
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Components of universal maps induced by diagram transformations

The complete comparison specifying `PseudoCone.mapDiagram` can be evaluated at any
vertex of the indexing bicategory. This file records the componentwise action of a
modification without introducing a second name for `Pseudofunctor.StrongTrans.isoApp`.

The construction is independent of a particular diagram shape. APIs for pseudopullbacks
and other concrete bilimits should specialize these declarations instead of rebuilding
the represented comparison componentwise.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E F : Pseudofunctor J B}

/-- At a diagram vertex, comparing the apex `2`-morphism induced by a modification
recovers the postcomposed component, conjugated by the two universal comparisons. -/
@[simp]
theorem mapDiagram.comparison.map₂_app
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    {α β : E ⟶ F} (Γ : α ⟶ β) (j : J) :
    ((T.comparison S.pt).map
        (mapDiagram.map₂ S T Γ)).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapDiagram.comparisonIso S T α) j).hom ≫
        (postcomposeModification Γ S).as.app j ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapDiagram.comparisonIso S T β) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

The pointwise formula evaluates the existing complete universal comparison with
`Pseudofunctor.StrongTrans.isoApp`; no new apex map, cell, inverse, or witness is chosen. -/

end Bicategory.PseudoCone

end CategoryTheory
