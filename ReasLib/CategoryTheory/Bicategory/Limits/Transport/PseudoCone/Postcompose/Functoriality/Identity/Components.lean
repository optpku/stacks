/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Components of identity coherence for universal diagram maps

The identity presentation for a universal map can be evaluated at every vertex of an
arbitrary indexing bicategory. Its component is the canonical conjugating isomorphism
for the componentwise formulas of `PseudoCone.mapDiagram.id.iso`.

This shape-independent layer is intended to be specialized by concrete bilimits. It
keeps walking-cospan projections and other shape-specific observations out of the
generic identity construction.
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
variable {E : Pseudofunctor J B}

/-- At a diagram vertex, the forward identity coherence is conjugated by the identity
presentation and the universal comparison. -/
@[simp]
theorem mapDiagram.id.iso.map_hom_app
    (S : PseudoCone E) [S.IsBilimit] (j : J) :
    ((S.comparison S.pt).map
        (mapDiagram.id.iso S).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapDiagram.id.comparisonIso S) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapDiagram.comparisonIso S S (𝟙 E)) j).inv := sorry

/-- At a diagram vertex, the inverse identity coherence is conjugated by the universal
comparison and the inverse identity presentation. -/
@[simp]
theorem mapDiagram.id.iso.map_inv_app
    (S : PseudoCone E) [S.IsBilimit] (j : J) :
    ((S.comparison S.pt).map
        (mapDiagram.id.iso S).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapDiagram.comparisonIso S S (𝟙 E)) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapDiagram.id.comparisonIso S) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

The formulas evaluate the existing complete identity and universal presentations with
`Pseudofunctor.StrongTrans.isoApp`; no new apex map, cell, inverse, or witness is chosen. -/

end Bicategory.PseudoCone

end CategoryTheory
