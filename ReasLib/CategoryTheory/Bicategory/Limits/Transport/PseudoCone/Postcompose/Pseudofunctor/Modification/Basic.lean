/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification.Naturality

/-!
# Strong transformations induced by diagram modifications

For a modification `Γ : α ⟶ β` between strong transformations of
pseudodiagrams, postcomposition gives a contravariant strong transformation

`postcompose β ⟶ postcompose α`.

Its object components are `postcomposeModificationMap Γ`; its strong
naturality isomorphisms are `postcomposeModificationNaturality Γ`.  Identity
and vertical-composition comparisons are kept in separate modules so clients
can import this assembly layer without the target-hom pseudofunctor.
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

/-- The contravariant strong transformation between pseudocone
postcomposition pseudofunctors induced by a diagram modification. -/
abbrev postcomposeModificationStrongTrans
    {α β : Pseudofunctor.StrongTrans E F} (Γ : α ⟶ β) :
    Pseudofunctor.StrongTrans
      (postcompose β) (postcompose α) :=
  ColaxCostructuredArrow.postcompose.cellStrongTrans
    (Pseudofunctor.constDiagram J B) Γ

/-- The object component of modification-induced postcomposition is the
corresponding contravariant pseudocone morphism. -/
@[simp]
theorem postcomposeModificationStrongTrans_app
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) (S : PseudoCone E) :
    (postcomposeModificationStrongTrans Γ).app S =
      postcomposeModificationMap Γ S := sorry

/-- The strong naturality isomorphism of modification-induced postcomposition
is the explicit pseudocone naturality isomorphism. -/
@[simp]
theorem postcomposeModificationStrongTrans_naturality
    {α β : Pseudofunctor.StrongTrans E F}
    (Γ : α ⟶ β) {S T : PseudoCone E} (u : S ⟶ T) :
    (postcomposeModificationStrongTrans Γ).naturality u =
      postcomposeModificationNaturality Γ u := sorry

/- Data and axiom audit (mathlib 4.32):

`postcomposeModificationStrongTrans` is the transparent pseudocone specialization of
`ColaxCostructuredArrow.postcompose.cellStrongTrans`. Its components, naturality isomorphisms,
and strong-transformation coherence therefore have one canonical owner. -/

end Bicategory.PseudoCone

end CategoryTheory
