/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Identity functoriality of target-cell postcomposition

The contravariant strong transformation induced by an identity target cell is
the identity strong transformation of the corresponding costructured-arrow
postcomposition pseudofunctor.

The bundled equality is the functoriality statement. Its component and
naturality projections are recorded separately so downstream arguments can
simplify locally without unfolding a `Pseudofunctor.StrongTrans`.
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

/-- Target-cell postcomposition sends an identity cell to the identity strong
transformation. -/
@[simp]
theorem cellStrongTrans.id
    (K : Pseudofunctor A C) (f : X ⟶ Y) :
    cellStrongTrans K (𝟙 f) =
      Pseudofunctor.StrongTrans.id
        (postcompose K f) := by
  have h : cellComponent (K := K) (𝟙 f) = fun S ↦ 𝟙 (obj f S) := by
    funext S
    refine ColaxComma.Hom.ext
      (f := cellComponent (K := K) (𝟙 f) S)
      (g := 𝟙 (obj f S)) rfl rfl ?_
    change (ColaxCostructuredArrow.fac (𝟙 (obj f S)) ≫
        cell (𝟙 f) S) ≫ (ρ_ (obj f S).hom).inv =
      (𝟙 (obj f S) : obj f S ⟶ obj f S).cell
    have hcell : cell (𝟙 f) S = 𝟙 (obj f S).hom :=
      (structuralFunctor Y S).map_id f
    simp only [hcell, Category.comp_id, ColaxCostructuredArrow.fac]
    exact (Category.assoc _ _ _).trans
      ((congrArg
        (fun η ↦ (𝟙 (obj f S) : obj f S ⟶ obj f S).cell ≫ η)
        (Iso.hom_inv_id (ρ_ (obj f S).hom))).trans (Category.comp_id _))
  have iso_hext {S T : ColaxCostructuredArrow K Y}
      {u v u' v' : S ⟶ T} (hu : u = u') (hv : v = v')
      (e : u ≅ v) (e' : u' ≅ v')
      (hl : HEq (ColaxCostructuredArrow.map₂ e.hom)
        (ColaxCostructuredArrow.map₂ e'.hom)) : HEq e e' := by
    cases hu
    cases hv
    apply heq_of_eq
    apply Iso.ext
    apply ColaxComma.Hom₂.ext
    · exact eq_of_heq hl
    · exact Subsingleton.elim _ _
  unfold cellStrongTrans Pseudofunctor.StrongTrans.id
  congr! 1
  apply Function.hfunext rfl
  intro S S' hS
  cases (eq_of_heq hS)
  apply Function.hfunext rfl
  intro T T' hT
  cases (eq_of_heq hT)
  apply Function.hfunext rfl
  intro u u' hu
  cases (eq_of_heq hu)
  refine iso_hext
    (congrArg (fun v ↦ (postcompose K f).map u ≫ v) (congrFun h T))
    (congrArg (fun v ↦ v ≫ (postcompose K f).map u) (congrFun h S)) _ _ ?_
  rfl

/-- The component of the strong transformation induced by an identity target
cell is the identity costructured-arrow morphism. -/
@[simp]
theorem cellStrongTrans.id.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (cellStrongTrans K (𝟙 f)).app S =
      𝟙 (obj f S) := by
  exact congrArg
    (fun η : Pseudofunctor.StrongTrans (postcompose K f) (postcompose K f) ↦ η.app S)
    (cellStrongTrans.id K f)

namespace Implementation

/-- The identity source-map isomorphism underlying the component of the
target-cell identity comparison. -/
private def cellMapId.app.sourceIso
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
          (cellComponent (𝟙 f) S) ≅
      ColaxCostructuredArrow.map (K := K) (X := Y)
        (𝟙 (obj f S)) :=
  Iso.refl (𝟙 S.left)

/-- Compatibility of the identity source cell with the normalized comparison
cells of the target-cell identity component. -/
private theorem cellMapId.app.comm
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((obj f S).comparison S.left).map
          (cellMapId.app.sourceIso f S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (𝟙 (obj f S)) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (cellComponent (𝟙 f) S) := by
  change ((obj f S).comparison (obj f S).left).map
      (𝟙 (𝟙 (obj f S).left)) ≫
      ColaxCostructuredArrow.fac (𝟙 (obj f S)) =
    ColaxCostructuredArrow.fac (cellComponent (𝟙 f) S)
  rw [Functor.map_id, Category.id_comp]
  change ColaxCostructuredArrow.fac (𝟙 (obj f S)) =
    ((ColaxCostructuredArrow.fac (𝟙 (obj f S)) ≫ cell (𝟙 f) S) ≫
      (ρ_ (obj f S).hom).inv) ≫ (ρ_ (obj f S).hom).hom
  have hcell : cell (𝟙 f) S = 𝟙 (obj f S).hom :=
    (structuralFunctor Y S).map_id f
  rw [hcell, Category.comp_id]
  exact ((Category.assoc _ _ _).trans
    ((congrArg (fun η ↦ ColaxCostructuredArrow.fac (𝟙 (obj f S)) ≫ η)
      (Iso.inv_hom_id (ρ_ (obj f S).hom))).trans (Category.comp_id _))).symm

end Implementation

/-- The pointwise isomorphism from the component induced by an identity
target cell to the identity costructured-arrow morphism.

Both its forward and inverse source cells are identities. -/
def cellMapId.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    cellComponent (𝟙 f) S ≅
      𝟙 (obj f S) :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.cellMapId.app.sourceIso f S)
    (Implementation.cellMapId.app.comm f S)

namespace Implementation

/-- Naturality of the pointwise identity comparisons with respect to
costructured-arrow morphisms. -/
private theorem cellMapId.naturality
    (f : X ⟶ Y) :
    ∀ {S T : ColaxCostructuredArrow K X} (u : S ⟶ T),
      (postcompose K f).map u ◁
    (cellMapId.app f T).hom ≫
          ((Pseudofunctor.StrongTrans.id
            (postcompose K f)).naturality u).hom =
          ((cellStrongTrans K (𝟙 f)).naturality u).hom ≫
          (cellMapId.app f S).hom ▷
            (postcompose K f).map u := by
  intro S T u
  apply ColaxComma.Hom₂.ext
  · change (u.left ◁ 𝟙 (𝟙 T.left)) ≫
        ((ρ_ u.left).hom ≫ (λ_ u.left).inv) =
      ((ρ_ u.left).hom ≫ (λ_ u.left).inv) ≫
        (𝟙 (𝟙 S.left) ▷ u.left)
    simp only [whiskerLeft_id, id_whiskerRight, Category.id_comp,
      Category.comp_id]
  · exact Subsingleton.elim _ _

end Implementation

/-- The pseudofunctor identity comparison for contravariant target-cell
postcomposition.

Its components are the explicit isomorphisms
`postcompose.cellMapId.app f S`; no equality transport is used to select the
component `2`-cells. -/
def cellMapId
    (K : Pseudofunctor A C) (f : X ⟶ Y) :
    @Iso
      (postcompose K f ⟶ postcompose K f)
      Pseudofunctor.StrongTrans.homCategoryOwner
      (cellStrongTrans K (𝟙 f))
      (Pseudofunctor.StrongTrans.id
        (postcompose K f)) :=
  Pseudofunctor.StrongTrans.isoMk
    (cellMapId.app f)
    (Implementation.cellMapId.naturality f)

/-- The forward component of the target-cell identity comparison is the
explicit pointwise identity comparison. -/
@[simp]
theorem cellMapId.hom.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (cellMapId K f).hom.as.app S =
      (cellMapId.app f S).hom := rfl

/-- The inverse component of the target-cell identity comparison is the
inverse explicit pointwise identity comparison. -/
@[simp]
theorem cellMapId.inv.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (cellMapId K f).inv.as.app S =
      (cellMapId.app f S).inv := rfl

/-- The source cell of every forward component of the target-cell identity
comparison is the identity `2`-morphism. -/
@[simp]
theorem cellMapId.hom.app.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellMapId K f).hom.as.app S) =
      𝟙 (𝟙 S.left) := rfl

/-- The source cell of every inverse component of the target-cell identity
comparison is the identity `2`-morphism. -/
@[simp]
theorem cellMapId.inv.app.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellMapId K f).inv.as.app S) =
      𝟙 (𝟙 S.left) := rfl

/-- The forward source cell of naturality for an identity target cell is the
standard right-to-left unitor comparison. -/
@[simp]
theorem cellStrongTrans.id.naturality.hom.map₂
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellStrongTrans K (𝟙 f)).naturality u).hom =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).hom := rfl

/-- The inverse source cell of naturality for an identity target cell is the
inverse standard unitor comparison. -/
@[simp]
theorem cellStrongTrans.id.naturality.inv.map₂
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((cellStrongTrans K (𝟙 f)).naturality u).inv =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).inv := rfl

/- Axiom audit (mathlib 4.32):

`postcompose.cellMapId.app` is built by `ColaxCostructuredArrow.iso₂Mk` from the
explicit identity source-map isomorphism. `postcompose.cellMapId` is then built
by `Pseudofunctor.StrongTrans.isoMk` from those explicit pointwise
isomorphisms. Compatibility, modification naturality, and all projection
equalities in this file are proved. Imported proof-only coherence obligations
remain in the axiom footprint; no component `2`-morphism is selected through a
proof placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
