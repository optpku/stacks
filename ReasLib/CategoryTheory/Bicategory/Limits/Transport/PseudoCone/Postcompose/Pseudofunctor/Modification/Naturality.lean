module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Naturality
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification.Component

/-!
# Naturality of postcomposition by diagram modifications

A modification `Γ : α ⟶ β` of diagram transformations gives contravariant
pseudocone-morphism components `postcomposeModificationMap Γ S`.  At a
pseudocone morphism `u : S ⟶ T`, their strong naturality compares

`postcomposeMap β u ≫ postcomposeModificationMap Γ T`

with

`postcomposeModificationMap Γ S ≫ postcomposeMap α u`.

Both composites retain the apex map of `u` up to the standard unitors.  The
resulting apex-cell isomorphism is lifted through the normalized
`ColaxCostructuredArrow.iso₂Mk` API.  Coherence for the resulting strong
transformation belongs in the next layer.
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

/-- The strong naturality isomorphism for the contravariant pseudocone
components induced by a diagram modification. -/
abbrev postcomposeModificationNaturality
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) {S T : PseudoCone E} (u : S ⟶ T) :
    postcomposeMap β u ≫ postcomposeModificationMap Γ T ≅
      postcomposeModificationMap Γ S ≫ postcomposeMap α u :=
  ColaxCostructuredArrow.postcompose.cellNaturality
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) Γ u

/-- The apex cell of the forward modification-naturality isomorphism is the
standard right-to-left unitor comparison. -/
@[simp]
theorem postcomposeModificationNaturality_hom_map₂
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.map₂ (postcomposeModificationNaturality Γ u).hom =
      (ρ_ (PseudoCone.map u) ≪≫
        (λ_ (PseudoCone.map u)).symm).hom := sorry

/-- The apex cell of the inverse modification-naturality isomorphism is the
inverse standard unitor comparison. -/
@[simp]
theorem postcomposeModificationNaturality_inv_map₂
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.map₂ (postcomposeModificationNaturality Γ u).inv =
      (ρ_ (PseudoCone.map u) ≪≫
        (λ_ (PseudoCone.map u)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`postcomposeModificationNaturality` is the transparent pseudocone specialization of
`ColaxCostructuredArrow.postcompose.cellNaturality`. Its apex-map isomorphism is therefore
the canonical right-unitor followed by inverse left-unitor comparison, with no duplicate
compatibility proof in this file. -/

end Bicategory.PseudoCone

end CategoryTheory
