module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Basic

/-!
# Universal maps induced by transformations of diagrams

A strong transformation of diagrams postcomposes any source pseudocone. When the target
pseudocone is a bilimit, its universal property then supplies a map between the apexes.

This file exposes that construction functorially in diagram transformations and
modifications. Identity and composition comparisons for successive diagram
transformations are kept in separate functoriality modules.
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

/-- The universal apex map induced by a strong transformation of diagrams.

The source pseudocone is first postcomposed with the transformation and then lifted into
the bilimit target pseudocone. This is the shape-independent owner specialized by
constructions such as maps between pseudopullbacks. -/
noncomputable abbrev mapDiagram
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    (α : E ⟶ F) : S.pt ⟶ T.pt :=
  PseudoCone.lift (postcomposeObj α S) T

/-- The complete cone-transformation comparison specifying the universal map induced by a
diagram transformation. -/
noncomputable abbrev mapDiagram.comparisonIso
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    (α : E ⟶ F) :
    (T.comparison S.pt).obj (mapDiagram S T α) ≅
      (postcomposeObj α S).π :=
  PseudoCone.lift.comparisonIso (postcomposeObj α S) T

/-- Universal apex maps from a fixed source pseudocone to a bilimit target pseudocone are
functorial in transformations of the diagram.

This is the composite of the postcomposition functor for the source pseudocone and the
single chosen lift functor represented by the target bilimit. -/
noncomputable abbrev mapDiagram.functor
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit] :
    (E ⟶ F) ⥤ (S.pt ⟶ T.pt) :=
  postcomposeTransformationFunctor F S ⋙
    PseudoCone.lift.functor T S.pt

/-- A modification between diagram transformations induces a `2`-morphism between their
universal apex maps. -/
noncomputable abbrev mapDiagram.map₂
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    {α β : E ⟶ F} (Γ : α ⟶ β) :
    mapDiagram S T α ⟶ mapDiagram S T β :=
  (PseudoCone.lift.functor T S.pt).map
    (postcomposeModification Γ S)

/-- The object action of `mapDiagram.functor` is the universal map induced by the supplied
diagram transformation. -/
@[simp]
theorem mapDiagram.functor.obj
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    (α : E ⟶ F) :
    (mapDiagram.functor S T).obj α =
      mapDiagram S T α := sorry

/-- The morphism action of `mapDiagram.functor` is the induced apex `2`-morphism. -/
@[simp]
theorem mapDiagram.functor.map
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    {α β : E ⟶ F} (Γ : α ⟶ β) :
    (mapDiagram.functor S T).map Γ =
      mapDiagram.map₂ S T Γ := sorry

/-- Applying the represented comparison to a `2`-morphism induced by a diagram modification
recovers the postcomposed modification, conjugated by the two universal comparison
isomorphisms. -/
@[simp]
theorem mapDiagram.comparison.map₂
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    {α β : E ⟶ F} (Γ : α ⟶ β) :
    (T.comparison S.pt).map (mapDiagram.map₂ S T Γ) =
      (mapDiagram.comparisonIso S T α).hom ≫
        postcomposeModification Γ S ≫
        (mapDiagram.comparisonIso S T β).inv := sorry

/-- The induced apex `2`-morphism sends an identity diagram modification to an identity
cell. -/
@[simp]
theorem mapDiagram.map₂.id
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    (α : E ⟶ F) :
    mapDiagram.map₂ S T (𝟙 α) =
      𝟙 (mapDiagram S T α) := sorry

/-- The induced apex `2`-morphism preserves vertical composition of diagram
modifications. -/
@[simp]
theorem mapDiagram.map₂.comp
    (S : PseudoCone E) (T : PseudoCone F) [T.IsBilimit]
    {α β γ : E ⟶ F} (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    mapDiagram.map₂ S T (Γ ≫ Δ) =
      mapDiagram.map₂ S T Γ ≫ mapDiagram.map₂ S T Δ := sorry

/- Data and axiom audit (mathlib 4.32):

`mapDiagram` and `mapDiagram.map₂` reuse the single quasi-inverse functor selected by
`PseudoCone.lift.functor`; `mapDiagram.comparisonIso` is its counit specification.
`mapDiagram.functor` is their explicit functorial composite. No additional witness choice
is exposed, and downstream users can reason through the comparison and functoriality API
without unfolding the selected quasi-inverse. -/

end Bicategory.PseudoCone

end CategoryTheory
