/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Presentation.Construction

/-!
# Constructing modifications acting on readable changed-cospan cones

A modification between parallel cospan transformations acts on the cone transformation of
a fixed readable pseudopullback cone. The action is obtained by conjugating the neutral
`PseudoCone.postcomposeModification` with the readable/generic presentation isomorphisms.

This leaf owns the concrete modification data. Its component and functoriality formulas are
kept in `Modification.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Act on the cone transformation of a readable pseudopullback cone by a modification
between parallel cospan transformations.

The neutral postcomposition modification is conjugated by the two explicit
readable/generic presentation isomorphisms. -/
def changeCospan.modification
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    (S.changeCospan ψ).toPseudoCone.π ⟶
      (S.changeCospan φ).toPseudoCone.π :=
  (changeCospan.presentation.modification.iso S ψ).hom ≫
    PseudoCone.postcomposeModification Γ S.toPseudoCone ≫
    (changeCospan.presentation.modification.iso S φ).inv

/- Data and axiom audit (mathlib 4.32):

`changeCospan.modification` is the explicit three-stage conjugation above. Its middle
factor is the neutral `PseudoCone.postcomposeModification`; the two outer factors are the
explicit presentation isomorphisms. No component cell is reconstructed or selected in
this module. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
