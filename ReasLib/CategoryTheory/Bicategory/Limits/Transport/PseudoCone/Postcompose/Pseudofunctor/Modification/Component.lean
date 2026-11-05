/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Component
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Basic

/-!
# Components induced by modifications of diagram transformations

A modification `Γ : α ⟶ β` between diagram transformations induces a morphism between
the corresponding postcomposed pseudocones. Because morphisms of conical pseudocones
carry a colax comparison into their source cone, this component has the contravariant
direction

`postcomposeObj β S ⟶ postcomposeObj α S`.

Its apex map is the identity. Its comparison is the identity-cone comparison followed
by left whiskering of `Γ`. This file isolates that explicit component before it is
assembled into a strong transformation between postcomposition pseudofunctors.
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

/-- The contravariant pseudocone-morphism component induced by a modification of
diagram transformations.

The apex map is `𝟙 S.pt`. The comparison first identifies the comparison of that
identity map with `(postcomposeObj α S).π`, then applies the left-whiskered
modification from `α` to `β`. -/
abbrev postcomposeModificationMap
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) :
    postcomposeObj β S ⟶ postcomposeObj α S :=
  ColaxCostructuredArrow.postcompose.cellComponent
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) Γ S

/-- A modification component acts by the identity on the pseudocone apex. -/
@[simp]
theorem postcomposeModificationMap_map
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) :
    PseudoCone.map (postcomposeModificationMap Γ S) =
      𝟙 S.pt := sorry

/-- The comparison of a modification component is the identity-cone comparison followed
by the left-whiskered diagram modification. -/
@[simp]
theorem postcomposeModificationMap_fac
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) :
    PseudoCone.fac (postcomposeModificationMap Γ S) =
      PseudoCone.fac (𝟙 (postcomposeObj α S)) ≫
        postcomposeModification Γ S := sorry

/-- At a diagram vertex, the comparison of a modification component is the
identity-cone comparison followed by ordinary left whiskering by `Γ`. -/
@[simp]
theorem postcomposeModificationMap_fac_app
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) (j : J) :
    (PseudoCone.fac
        (postcomposeModificationMap Γ S)).as.app j =
      (PseudoCone.fac
          (𝟙 (postcomposeObj α S))).as.app j ≫
        S.π.app j ◁ Γ.as.app j := sorry

/-- The component induced by an identity diagram modification is the identity
pseudocone morphism. -/
@[simp]
theorem postcomposeModificationMap_id
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    postcomposeModificationMap (𝟙 α) S =
      𝟙 (postcomposeObj α S) := sorry

/-- Components reverse vertical composition of diagram modifications up to the
canonical invertible comparison, with inverse right-unitor apex cell. -/
abbrev postcomposeModificationMap_comp
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    postcomposeModificationMap (Γ ≫ Δ) S ≅
      postcomposeModificationMap Δ S ≫
        postcomposeModificationMap Γ S :=
  ColaxCostructuredArrow.postcompose.cellComponent.comp
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) Γ Δ S

/- Data and axiom audit (mathlib 4.32):

`postcomposeModificationMap` has the explicit identity apex map. Its comparison is the
existing identity-cone comparison followed by `postcomposeModification`; no apex map,
comparison modification, inverse, or witness is selected through a proof placeholder.
The composition comparison reuses the explicit inverse right-unitor comparison
`cellComponent.comp`; the remaining theorems only expose projections and identities. -/

end Bicategory.PseudoCone

end CategoryTheory
