/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete

/-!
# Transformation-hom pseudofunctor for pseudocone postcomposition

For fixed pseudodiagrams `E F : J ⥤ᵖ B`, postcomposition of pseudocones is
contravariantly pseudofunctorial in a strong transformation `E ⟶ F` and its
modifications. The canonical source is the locally discrete bicategory on the
opposite modification category `(Pseudofunctor.StrongTrans E F)ᵒᵖ`.

Objects act by `postcompose`; a modification in the opposite category acts by
`postcomposeModificationStrongTrans` after `unop`. The identity and
composition comparisons are owned directly by the canonical
`ColaxCostructuredArrow` pseudofunctor. Projection formulas are kept in
`Modification.Pseudofunctor.Computations`.
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

variable (E F) in
/-- Postcomposition of conical pseudocones as a pseudofunctor on the opposite
modification category of strong transformations `E ⟶ F`.

Contravariance is absorbed into the domain
`(Pseudofunctor.StrongTrans E F)ᵒᵖ`, so its modification action has the
ordinary pseudofunctor direction. -/
abbrev postcomposeModificationPseudofunctor :
    LocallyDiscrete ((Pseudofunctor.StrongTrans E F)ᵒᵖ) ⥤ᵖ
      Pseudofunctor (PseudoCone E) (PseudoCone F) :=
  ColaxCostructuredArrow.postcompose.pseudofunctor
    (Pseudofunctor.constDiagram J B) E F

/- Data and axiom audit (mathlib 4.32):

`postcomposeModificationPseudofunctor` is the transparent pseudocone specialization of
`ColaxCostructuredArrow.postcompose.pseudofunctor`. Its object, modification, comparison,
and coherence data therefore have a single canonical owner. -/

end Bicategory.PseudoCone

end CategoryTheory
