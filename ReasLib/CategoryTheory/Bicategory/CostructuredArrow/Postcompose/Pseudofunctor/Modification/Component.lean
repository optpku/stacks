/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic

/-!
# Components induced by target 2-morphisms

For a fixed pseudofunctor `K : A ⥤ᵖ C`, a target `2`-morphism
`η : f ⟶ g` induces a morphism between the corresponding postcomposed
colax costructured arrows. The colax orientation reverses the target cell:

`postcompose.obj g S ⟶ postcompose.obj f S`.

Its source map is the identity of `S.left`. Its normalized comparison first
uses the comparison of the identity morphism of `postcompose.obj f S` and then
applies the target cell through `postcompose.cell`.

This file contains only the component data and its elementary functoriality.
Naturality in costructured-arrow morphisms and assembly into a strong
transformation belong in separate downstream modules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

/-- The contravariant costructured-arrow component induced by a target
`2`-morphism.

For `η : f ⟶ g`, the source map is `𝟙 S.left`. Its normalized comparison
continues the comparison of `𝟙 (postcompose.obj f S)` with the structural cell
`postcompose.cell η S`. -/
def cellComponent
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    obj g S ⟶ obj f S :=
  ColaxCostructuredArrow.homMk (K := K) (X := Y)
    (𝟙 S.left)
    (ColaxCostructuredArrow.fac (K := K) (X := Y)
        (𝟙 (obj f S)) ≫
      cell η S)

/-- A component induced by a target `2`-morphism acts by the identity on the
source object. -/
@[simp]
theorem cellComponent.map
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
        (cellComponent η S) =
      𝟙 S.left := sorry

/-- The normalized comparison of a component induced by a target cell is the
identity comparison followed by the postcomposed structural cell. -/
@[simp]
theorem cellComponent.fac
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := Y)
        (cellComponent η S) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
          (𝟙 (obj f S)) ≫
        cell η S := sorry

/-- The component induced by an identity target cell is the identity
costructured-arrow morphism. -/
@[simp]
theorem cellComponent.id
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    cellComponent (𝟙 f) S =
      𝟙 (obj f S) := sorry

/-- Components reverse vertical composition of target cells, as forced by the
colax orientation of costructured-arrow morphisms. -/
@[simp]
theorem cellComponent.comp
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    cellComponent (η ≫ θ) S =
      cellComponent θ S ≫
        cellComponent η S := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.cellComponent` has the explicit source map `𝟙 S.left`. Its
normalized comparison is the existing identity comparison followed by
`postcompose.cell η S`, whose data are inherited from mathlib's postcomposition
functor. No source map, structural cell, or comparison is selected through a
proof placeholder. The remaining declarations are `Prop`-valued projection
and functoriality statements. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
