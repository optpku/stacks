module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic

/-!
# Postcomposing conical pseudocones by diagram transformations

This file contains the shape-independent object action of a strong transformation on
conical pseudocones. It also records the action of diagram modifications after fixing the
source pseudocone.

Transport of pseudocone morphisms, functoriality in the pseudocone variable, and universal
maps into bilimit cones belong to downstream modules. Keeping those layers separate makes
this basic diagram-transformation API usable without importing bilimit choices.
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

/-- Postcompose a conical pseudocone by a strong transformation of diagrams.

This is the bicategorical object-level analogue of `CategoryTheory.Limits.Cone.postcompose`.
It preserves the apex and vertically composes the cone transformation with the supplied
diagram transformation. -/
abbrev postcomposeObj (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    PseudoCone F :=
  ColaxCostructuredArrow.postcompose.obj α S

/-- Postcomposition by a diagram transformation does not change the pseudocone apex. -/
@[simp]
theorem postcomposeObj_pt
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    (postcomposeObj α S).pt = S.pt := sorry

/-- The transformation of a postcomposed pseudocone is vertical composition with the
diagram transformation. -/
@[simp]
theorem postcomposeObj_π
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    (postcomposeObj α S).π = S.π ≫ α := sorry

/-- Whisker a modification between diagram transformations on the left by the
transformation of a fixed conical pseudocone. -/
abbrev postcomposeModification
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : Pseudofunctor.StrongTrans.Hom α β) (S : PseudoCone E) :
    (postcomposeObj α S).π ⟶ (postcomposeObj β S).π :=
  ColaxCostructuredArrow.postcompose.cell Γ S

/-- At a diagram vertex, postcomposition by a modification is ordinary left whiskering by
the corresponding pseudocone component. -/
@[simp]
theorem postcomposeModification_app
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : Pseudofunctor.StrongTrans.Hom α β) (S : PseudoCone E) (j : J) :
    (postcomposeModification Γ S).as.app j =
      S.π.app j ◁ Γ.as.app j := sorry

/-- Postcomposition sends the identity diagram modification to the identity
modification. -/
@[simp]
theorem postcomposeModification_id
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    postcomposeModification (𝟙 α) S =
      𝟙 (postcomposeObj α S).π := sorry

/-- Postcomposition preserves vertical composition of diagram modifications. -/
@[simp]
theorem postcomposeModification_comp
    {α β γ : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) (S : PseudoCone E) :
    postcomposeModification (Γ ≫ Δ) S =
      postcomposeModification Γ S ≫
        postcomposeModification Δ S := sorry

variable (F) in
/-- Postcomposition of a fixed conical pseudocone is functorial in diagram
transformations and their modifications.

Its objects are the transformations of the postcomposed pseudocones; its morphisms are
the left-whiskered diagram modifications. -/
abbrev postcomposeTransformationFunctor (S : PseudoCone E) :
    (E ⟶ F) ⥤ (Pseudofunctor.const J S.pt ⟶ F) :=
  ColaxCostructuredArrow.postcompose.structuralFunctor F S

/-- The object action of `postcomposeTransformationFunctor` is the transformation of the
postcomposed pseudocone. -/
@[simp]
theorem postcomposeTransformationFunctor_obj
    (S : PseudoCone E) (α : E ⟶ F) :
    (postcomposeTransformationFunctor F S).obj α =
      (postcomposeObj α S).π := sorry

/-- The morphism action of `postcomposeTransformationFunctor` is postcomposition by the
diagram modification. -/
@[simp]
theorem postcomposeTransformationFunctor_map
    (S : PseudoCone E) {α β : E ⟶ F} (Γ : α ⟶ β) :
    (postcomposeTransformationFunctor F S).map Γ =
      postcomposeModification Γ S := sorry

/- Data and axiom audit (mathlib 4.32):

The three data-bearing declarations are transparent specializations of the canonical
`ColaxCostructuredArrow` postcomposition API. Thus the apex, transformation, modification,
and functor actions have a single owner. Any `sorryAx` dependency in this file is confined
to the readable `PseudoCone` projection and functoriality statements. -/

end Bicategory.PseudoCone

end CategoryTheory
