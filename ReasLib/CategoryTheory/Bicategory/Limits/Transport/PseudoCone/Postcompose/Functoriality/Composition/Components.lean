/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Components of composition coherence for universal diagram maps

The complete presentation for a composite universal map can be evaluated at every
vertex of an arbitrary indexing bicategory. Its component is the canonical conjugating
isomorphism for the componentwise formulas of `PseudoCone.mapDiagram.comp.iso`.

This shape-independent layer contains the common content behind projection calculations
for pseudopullbacks and analogous calculations for other concrete bilimits.
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
variable {E F G : Pseudofunctor J B}

/-- At a diagram vertex, the forward composition coherence is conjugated by the
composite presentation and the final universal comparison. -/
@[simp]
theorem mapDiagram.comp.iso.map_hom_app
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) (j : J) :
    ((U.comparison S.pt).map
        (mapDiagram.comp.iso S T U α β).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapDiagram.comp.comparisonIso S T U α β) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapDiagram.comparisonIso S U (α ≫ β)) j).inv := sorry

/-- At a diagram vertex, the inverse composition coherence is conjugated by the final
universal comparison and the inverse composite presentation. -/
@[simp]
theorem mapDiagram.comp.iso.map_inv_app
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) (j : J) :
    ((U.comparison S.pt).map
        (mapDiagram.comp.iso S T U α β).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapDiagram.comparisonIso S U (α ≫ β)) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapDiagram.comp.comparisonIso S T U α β) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

The formulas evaluate the existing complete composite and universal presentations with
`Pseudofunctor.StrongTrans.isoApp`; no new apex map, cell, inverse, or witness is chosen. -/

end Bicategory.PseudoCone

end CategoryTheory
