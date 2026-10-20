/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete

/-!
# Computations for modification postcomposition of pseudocones

This module exposes the raw locally-discrete fields and the base-facing
opposite-hom formulas of `postcomposeModificationPseudofunctor`. The latter
let applications work directly with strong transformations and modifications,
without repeating `op`, `unop`, or `LocallyDiscrete` bookkeeping.
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

namespace postcomposeModificationPseudofunctor

/-- The object action of modification postcomposition is postcomposition by
the underlying diagram transformation. -/
@[simp]
theorem obj
    {E F : Pseudofunctor J B}
    (α : (Pseudofunctor.StrongTrans E F)ᵒᵖ) :
    (postcomposeModificationPseudofunctor E F).obj
        (LocallyDiscrete.mk α) =
      postcompose α.unop := sorry

/-- The morphism action of modification postcomposition is the contravariant
strong transformation induced by the underlying diagram modification. -/
@[simp]
theorem map
    {E F : Pseudofunctor J B}
    {α β : (Pseudofunctor.StrongTrans E F)ᵒᵖ} (Γ : α ⟶ β) :
    (postcomposeModificationPseudofunctor E F).map Γ.toLoc =
      postcomposeModificationStrongTrans Γ.unop := sorry

/-- The identity comparison of modification postcomposition is the explicit
diagram-modification identity comparison. -/
@[simp]
theorem mapId
    {E F : Pseudofunctor J B}
    (α : (Pseudofunctor.StrongTrans E F)ᵒᵖ) :
    (postcomposeModificationPseudofunctor E F).mapId
        (LocallyDiscrete.mk α) =
      ColaxCostructuredArrow.postcompose.cellMapId
        (Pseudofunctor.constDiagram J B) α.unop := sorry

/-- The composition comparison of modification postcomposition is the explicit
comparison with the underlying modifications in reversed order. -/
@[simp]
theorem mapComp
    {E F : Pseudofunctor J B}
    {α β γ : (Pseudofunctor.StrongTrans E F)ᵒᵖ}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    (postcomposeModificationPseudofunctor E F).mapComp Γ.toLoc Δ.toLoc =
      ColaxCostructuredArrow.postcompose.cellMapComp
        (Pseudofunctor.constDiagram J B) Δ.unop Γ.unop := sorry

/-! Base-facing formulas for the opposite locally discrete domain. -/

namespace base

/-- The object action, written for an underlying strong transformation rather
than its opposite object. -/
@[simp]
theorem obj
    {E F : Pseudofunctor J B}
    (α : Pseudofunctor.StrongTrans E F) :
    (postcomposeModificationPseudofunctor E F).obj
        (LocallyDiscrete.mk (Opposite.op α)) =
      postcompose α := sorry

/-- The morphism action, written for an underlying diagram modification. -/
@[simp]
theorem map
    {E F : Pseudofunctor J B}
    {α β : Pseudofunctor.StrongTrans E F} (Γ : α ⟶ β) :
    (postcomposeModificationPseudofunctor E F).map Γ.op.toLoc =
      postcomposeModificationStrongTrans Γ := sorry

/-- The base-facing identity comparison is the explicit diagram-modification
identity comparison. -/
@[simp]
theorem mapId
    {E F : Pseudofunctor J B}
    (α : Pseudofunctor.StrongTrans E F) :
    (postcomposeModificationPseudofunctor E F).mapIdOp α =
      ColaxCostructuredArrow.postcompose.cellMapId
        (Pseudofunctor.constDiagram J B) α := sorry

/-- The base-facing composition comparison is the explicit comparison for the
reversed modification action. -/
@[simp]
theorem mapComp
    {E F : Pseudofunctor J B}
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    (postcomposeModificationPseudofunctor E F).mapCompOp Δ Γ =
      ColaxCostructuredArrow.postcompose.cellMapComp
        (Pseudofunctor.constDiagram J B) Γ Δ := sorry

/-! Component and apex-cell formulas for the base-facing action. -/

/-- The component of the base-facing modification action is the explicit
contravariant pseudocone morphism. -/
@[simp]
theorem map.app
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) :
    ((postcomposeModificationPseudofunctor E F).map Γ.op.toLoc).app S =
      postcomposeModificationMap Γ S := sorry

/-- The strong naturality of the base-facing modification action is the
explicit pseudocone naturality isomorphism. -/
@[simp]
theorem map.naturality
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) {S T : PseudoCone E} (u : S ⟶ T) :
    ((postcomposeModificationPseudofunctor E F).map
      Γ.op.toLoc).naturality u =
      postcomposeModificationNaturality Γ u := sorry

/-- The forward component of the base-facing identity comparison is the
explicit pointwise identity comparison. -/
@[simp]
theorem mapId.hom.app
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    ((postcomposeModificationPseudofunctor E F).mapIdOp α).hom.as.app S =
      (ColaxCostructuredArrow.postcompose.cellMapId.app
        (K := Pseudofunctor.constDiagram J B)
        (X := E) (Y := F) α S).hom := sorry

/-- The inverse component of the base-facing identity comparison is the
inverse explicit pointwise identity comparison. -/
@[simp]
theorem mapId.inv.app
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    ((postcomposeModificationPseudofunctor E F).mapIdOp α).inv.as.app S =
      (ColaxCostructuredArrow.postcompose.cellMapId.app
        (K := Pseudofunctor.constDiagram J B)
        (X := E) (Y := F) α S).inv := sorry

/-- The apex cell of a forward base-facing identity-comparison component is
the identity cell. -/
@[simp]
theorem mapId.hom.app.map₂
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    PseudoCone.map₂
        (((postcomposeModificationPseudofunctor E F).mapIdOp α).hom.as.app S) =
      𝟙 (𝟙 S.pt) := sorry

/-- The apex cell of an inverse base-facing identity-comparison component is
the identity cell. -/
@[simp]
theorem mapId.inv.app.map₂
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    PseudoCone.map₂
        (((postcomposeModificationPseudofunctor E F).mapIdOp α).inv.as.app S) =
      𝟙 (𝟙 S.pt) := sorry

/-- The forward component of the base-facing composition comparison is the
explicit pointwise composition comparison. -/
@[simp]
theorem mapComp.hom.app
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    ((postcomposeModificationPseudofunctor E F).mapCompOp Δ Γ).hom.as.app S =
      (ColaxCostructuredArrow.postcompose.cellMapComp.app
        (K := Pseudofunctor.constDiagram J B)
        (X := E) (Y := F) Γ Δ S).hom := sorry

/-- The inverse component of the base-facing composition comparison is the
inverse explicit pointwise composition comparison. -/
@[simp]
theorem mapComp.inv.app
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    ((postcomposeModificationPseudofunctor E F).mapCompOp Δ Γ).inv.as.app S =
      (ColaxCostructuredArrow.postcompose.cellMapComp.app
        (K := Pseudofunctor.constDiagram J B)
        (X := E) (Y := F) Γ Δ S).inv := sorry

/-- The apex cell of a forward base-facing composition-comparison component is
the inverse right-unitor cell on the unchanged identity apex map. -/
@[simp]
theorem mapComp.hom.app.map₂
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    PseudoCone.map₂
        (((postcomposeModificationPseudofunctor E F).mapCompOp Δ Γ).hom.as.app S) =
      (ρ_ (𝟙 S.pt)).inv := sorry

/-- The apex cell of an inverse base-facing composition-comparison component
is the right-unitor cell inverse to the chosen forward comparison. -/
@[simp]
theorem mapComp.inv.app.map₂
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    PseudoCone.map₂
        (((postcomposeModificationPseudofunctor E F).mapCompOp Δ Γ).inv.as.app S) =
      (ρ_ (𝟙 S.pt)).hom := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no data. Each theorem identifies a field or a nested
component of `postcomposeModificationPseudofunctor` with the explicit owner
from the preceding layers, so downstream users need not unfold its private
locally-discrete assembly. -/

end base

end postcomposeModificationPseudofunctor

end Bicategory.PseudoCone

end CategoryTheory
