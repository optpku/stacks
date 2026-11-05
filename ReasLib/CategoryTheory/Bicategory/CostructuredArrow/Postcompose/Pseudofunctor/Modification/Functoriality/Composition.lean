/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Composition functoriality of target-cell postcomposition

Target-cell postcomposition reverses vertical composition. For
`η : f ⟶ g` and `θ : g ⟶ h`, the strong transformation induced by
`η ≫ θ` is canonically isomorphic to the vertical composite of the
transformation induced by `θ` followed by the transformation induced by `η`.

The bundled invertible modification is accompanied by its object-component
comparison. These are the `mapComp` data for the pseudofunctor on the locally
discrete bicategory of the opposite target hom-category. No strict composition
equality is asserted.
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

/-- The pointwise composition comparison for contravariant target-cell
postcomposition, reusing the component-level canonical comparison. -/
abbrev cellMapComp.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    cellComponent (η ≫ θ) S ≅
      cellComponent θ S ≫
        cellComponent η S :=
  cellComponent.comp η θ S

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

/-- Target-cell postcomposition reverses vertical composition up to the
canonical invertible modification `cellMapComp`. -/
abbrev cellStrongTrans.comp
    (K : Pseudofunctor A C) {f g h : X ⟶ Y}
    (η : f ⟶ g) (θ : g ⟶ h) :
    @Iso
      (postcompose K h ⟶ postcompose K f)
      Pseudofunctor.StrongTrans.homCategoryOwner
      (cellStrongTrans K (η ≫ θ))
      (Pseudofunctor.StrongTrans.vcomp
        (cellStrongTrans K θ)
        (cellStrongTrans K η)) :=
  cellMapComp K η θ

/-- The object component of the invertible composition modification.
The source maps are compared by a unitor, rather than a strict equality. -/
abbrev cellStrongTrans.comp.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    (cellStrongTrans K (η ≫ θ)).app S ≅
      (cellStrongTrans K θ).app S ≫
        (cellStrongTrans K η).app S :=
  cellMapComp.app η θ S

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
