/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Composition functoriality of target-cell postcomposition

Target-cell postcomposition reverses vertical composition. For
`η : f ⟶ g` and `θ : g ⟶ h`, the strong transformation induced by
`η ≫ θ` is the vertical composite of the transformation induced by `θ`
followed by the transformation induced by `η`.

The bundled equality is accompanied by its object-component formula. This is
the local `map_comp` API needed to package target-cell postcomposition as a
functor out of the opposite target hom-category.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

/-- Target-cell postcomposition reverses vertical composition as vertical
composition of strong transformations. -/
@[simp]
theorem cellStrongTrans.comp
    (K : Pseudofunctor A C) {f g h : X ⟶ Y}
    (η : f ⟶ g) (θ : g ⟶ h) :
    cellStrongTrans K (η ≫ θ) =
      Pseudofunctor.StrongTrans.vcomp
        (cellStrongTrans K θ)
        (cellStrongTrans K η) := sorry

/-- Object components display the reversed vertical composition of target
cells as ordinary composition of costructured-arrow morphisms. -/
@[simp]
theorem cellStrongTrans.comp.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    (cellStrongTrans K (η ≫ θ)).app S =
      (cellStrongTrans K θ).app S ≫
      (cellStrongTrans K η).app S := sorry

namespace Implementation

/-- The source-map comparison underlying the pointwise composition comparison
for target-cell components. -/
private def cellMapComp.app.sourceIso
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
          (cellComponent (η ≫ θ) S) ≅
      ColaxCostructuredArrow.map (K := K) (X := Y)
        (cellComponent θ S ≫
          cellComponent η S) :=
  (ρ_ (𝟙 S.left)).symm

/-- Compatibility of the source-map comparison with the normalized
costructured-arrow comparison cells. -/
private theorem cellMapComp.app.comm
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ((obj f S).comparison S.left).map
          (cellMapComp.app.sourceIso η θ S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (cellComponent θ S ≫
            cellComponent η S) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (cellComponent (η ≫ θ) S) := sorry

end Implementation

/-- The pointwise composition comparison for contravariant target-cell
postcomposition. -/
def cellMapComp.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    cellComponent (η ≫ θ) S ≅
      cellComponent θ S ≫
        cellComponent η S :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.cellMapComp.app.sourceIso η θ S)
    (Implementation.cellMapComp.app.comm η θ S)

namespace Implementation

/-- Naturality of the pointwise composition comparisons with respect to
costructured-arrow morphisms. -/
private theorem cellMapComp.naturality
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h) :
    ∀ {S T : ColaxCostructuredArrow K X} (u : S ⟶ T),
      (postcompose K h).map u ◁
            (cellMapComp.app η θ T).hom ≫
          ((Pseudofunctor.StrongTrans.vcomp
            (cellStrongTrans K θ)
            (cellStrongTrans K η)).naturality u).hom =
        ((cellStrongTrans K (η ≫ θ)).naturality u).hom ≫
          (cellMapComp.app η θ S).hom ▷
            (postcompose K f).map u := sorry

end Implementation

/-- The pseudofunctor composition comparison for contravariant target-cell
postcomposition.

The source-cell comparison is retained explicitly in each pointwise component;
the bundled isomorphism only assembles those components into a strong
transformation isomorphism. -/
def cellMapComp
    (K : Pseudofunctor A C) {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h) :
    @Iso
      (postcompose K h ⟶ postcompose K f)
      Pseudofunctor.StrongTrans.homCategoryOwner
      (cellStrongTrans K (η ≫ θ))
      (Pseudofunctor.StrongTrans.vcomp
        (cellStrongTrans K θ)
        (cellStrongTrans K η)) :=
  Pseudofunctor.StrongTrans.isoMk
    (cellMapComp.app η θ)
    (Implementation.cellMapComp.naturality η θ)

/-- The forward component of the target-cell composition comparison is the
explicit pointwise composition comparison. -/
@[simp]
theorem cellMapComp.hom.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    (cellMapComp K η θ).hom.as.app S =
      (cellMapComp.app η θ S).hom := sorry

/-- The inverse component of the target-cell composition comparison is the
inverse explicit pointwise composition comparison. -/
@[simp]
theorem cellMapComp.inv.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    (cellMapComp K η θ).inv.as.app S =
      (cellMapComp.app η θ S).inv := sorry

/-- The source cell of the forward pointwise composition comparison is the
inverse right-unitor cell on the unchanged source map. -/
@[simp]
theorem cellMapComp.hom.app.map₂
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellMapComp K η θ).hom.as.app S) =
      (ρ_ (𝟙 S.left)).inv := sorry

/-- The source cell of the inverse pointwise composition comparison is the
right-unitor cell inverse to the chosen forward source comparison. -/
@[simp]
theorem cellMapComp.inv.app.map₂
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellMapComp K η θ).inv.as.app S) =
      (ρ_ (𝟙 S.left)).hom := sorry

/- Axiom audit (mathlib 4.32):

`postcompose.cellMapComp.app` is built by `ColaxCostructuredArrow.iso₂Mk` from
the explicit inverse right-unitor on the unchanged source map. The bundled
`postcompose.cellMapComp` reuses the canonical
`Pseudofunctor.StrongTrans.vcomp` and only supplies modification naturality.
No source `2`-cell or inverse is selected through a proof placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
