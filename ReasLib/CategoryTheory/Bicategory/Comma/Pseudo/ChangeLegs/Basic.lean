/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.Iso

/-!
# Changing the legs of a pseudo comma bicategory

A pseudo comma construction is contravariant in its left leg and covariant in
its right leg. This leaf owns the concrete object, morphism, and cell actions
of a pair of strong transformations with those variances. Pseudofunctor
assembly and projection computations live in separate leaves.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace PseudoComma

variable {F F' : A ⥤ᵖ C} {G G' : B ⥤ᵖ C}

/-- Change both legs of a pseudo comma object by a contravariant strong
transformation on the left and a covariant strong transformation on the
right.

For `α : F' ⟶ F` and `β : G ⟶ G'`, the structural map is
`α.app S.left ≫ S.hom ≫ β.app S.right`. -/
def changeLegs.obj
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    PseudoComma F' G' :=
  ColaxComma.mk (ColaxComma.left S) (ColaxComma.right S)
    (α.app (ColaxComma.left S) ≫ ColaxComma.hom S ≫
      β.app (ColaxComma.right S))

/-- Changing pseudo comma legs retains the left endpoint object. -/
@[simp]
theorem changeLegs.obj.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    ColaxComma.left (changeLegs.obj α β S) = ColaxComma.left S := sorry

/-- Changing pseudo comma legs retains the right endpoint object. -/
@[simp]
theorem changeLegs.obj.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    ColaxComma.right (changeLegs.obj α β S) = ColaxComma.right S := sorry

/-- The structural map after changing pseudo comma legs is the explicit
left-transformation, original structural-map, right-transformation composite. -/
@[simp]
theorem changeLegs.obj.hom
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    ColaxComma.hom (changeLegs.obj α β S) =
      α.app (ColaxComma.left S) ≫ ColaxComma.hom S ≫
        β.app (ColaxComma.right S) := sorry

/-- The invertible comparison cell for a pseudo comma morphism after changing
both legs.

This is the canonical non-`Prop` owner of the pasted comparison used by
`changeLegs.map`; downstream constructions may reuse it without unfolding the
pseudo comma morphism. -/
noncomputable def changeLegs.cellIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    F'.map (left (F := F) (G := G) u) ≫
        ColaxComma.hom (changeLegs.obj α β T) ≅
      ColaxComma.hom (changeLegs.obj α β S) ≫
        G'.map (right (F := F) (G := G) u) :=
  (α_ (F'.map (left (F := F) (G := G) u))
    (α.app (ColaxComma.left T))
    (ColaxComma.hom T ≫ β.app (ColaxComma.right T))).symm ≪≫
    whiskerRightIso (α.naturality (left (F := F) (G := G) u))
      (ColaxComma.hom T ≫ β.app (ColaxComma.right T)) ≪≫
    α_ (α.app (ColaxComma.left S)) (F.map (left (F := F) (G := G) u))
      (ColaxComma.hom T ≫ β.app (ColaxComma.right T)) ≪≫
    whiskerLeftIso (α.app (ColaxComma.left S))
      (α_ (F.map (left (F := F) (G := G) u)) (ColaxComma.hom T)
        (β.app (ColaxComma.right T))).symm ≪≫
    whiskerLeftIso (α.app (ColaxComma.left S))
      (whiskerRightIso (PseudoComma.cellIso (F := F) (G := G) u)
        (β.app (ColaxComma.right T))) ≪≫
    whiskerLeftIso (α.app (ColaxComma.left S))
      (α_ (ColaxComma.hom S) (G.map (right (F := F) (G := G) u))
        (β.app (ColaxComma.right T))) ≪≫
    whiskerLeftIso (α.app (ColaxComma.left S))
      (whiskerLeftIso (ColaxComma.hom S)
        (β.naturality (right (F := F) (G := G) u))) ≪≫
    whiskerLeftIso (α.app (ColaxComma.left S))
      (α_ (ColaxComma.hom S) (β.app (ColaxComma.right S))
        (G'.map (right (F := F) (G := G) u))).symm ≪≫
    (α_ (α.app (ColaxComma.left S))
      (ColaxComma.hom S ≫ β.app (ColaxComma.right S))
      (G'.map (right (F := F) (G := G) u))).symm

/-- Change both legs of a pseudo comma morphism.

The endpoint maps are unchanged. Its invertible comparison cell is obtained by
pasting the two strong-transformation naturality isomorphisms with the
selected pseudo comma comparison. -/
noncomputable def changeLegs.map
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    changeLegs.obj α β S ⟶ changeLegs.obj α β T :=
  homMk (F := F') (G := G')
    (left (F := F) (G := G) u)
    (right (F := F) (G := G) u)
    (changeLegs.cellIso α β u)

/-- Changing pseudo comma legs leaves the left endpoint map unchanged. -/
@[simp]
theorem changeLegs.map.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    left (F := F') (G := G') (changeLegs.map α β u) =
      left (F := F) (G := G) u := sorry

/-- Changing pseudo comma legs leaves the right endpoint map unchanged. -/
@[simp]
theorem changeLegs.map.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    right (F := F') (G := G') (changeLegs.map α β u) =
      right (F := F) (G := G) u := sorry

/-- The selected comparison of a pseudo comma morphism after changing both
legs is the explicit pasted comparison isomorphism. -/
@[simp]
theorem changeLegs.map.cellIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    PseudoComma.cellIso (F := F') (G := G') (changeLegs.map α β u) =
      changeLegs.cellIso α β u := sorry

/-- The structural cell of a changed-leg pseudo comma morphism is the forward
cell of the canonical pasted comparison. -/
@[simp]
theorem changeLegs.map.cell
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    cell (F := F') (G := G') (changeLegs.map α β u) =
      (changeLegs.cellIso α β u).hom := sorry

namespace Implementation

/-- The unchanged endpoint cells of a pseudo comma cell remain compatible
after changing both legs. -/
private theorem map₂_w
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v : S ⟶ T} (η : u ⟶ v) :
    (F'.map₂ (left₂ (F := F) (G := G) η) ▷
        ColaxComma.hom (changeLegs.obj α β T)) ≫
        cell (F := F') (G := G') (changeLegs.map α β v) =
      cell (F := F') (G := G') (changeLegs.map α β u) ≫
        (ColaxComma.hom (changeLegs.obj α β S) ◁
          G'.map₂ (right₂ (F := F) (G := G) η)) := sorry

end Implementation

/-- Change both legs of a pseudo comma `2`-morphism. Its two endpoint cells
are retained literally. -/
noncomputable def changeLegs.map₂
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v : S ⟶ T} (η : u ⟶ v) :
    changeLegs.map α β u ⟶ changeLegs.map α β v :=
  hom₂Mk (F := F') (G := G')
    (left₂ (F := F) (G := G) η)
    (right₂ (F := F) (G := G) η)
    (Implementation.map₂_w α β η)

/-- Changing pseudo comma legs leaves the left endpoint cell unchanged. -/
@[simp]
theorem changeLegs.map₂.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v : S ⟶ T} (η : u ⟶ v) :
    left₂ (F := F') (G := G') (changeLegs.map₂ α β η) =
      left₂ (F := F) (G := G) η := sorry

/-- Changing pseudo comma legs leaves the right endpoint cell unchanged. -/
@[simp]
theorem changeLegs.map₂.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v : S ⟶ T} (η : u ⟶ v) :
    right₂ (F := F') (G := G') (changeLegs.map₂ α β η) =
      right₂ (F := F) (G := G) η := sorry

/- Data and axiom audit (mathlib 4.32):

`changeLegs.obj` stores the explicit triple structural composite, and
`changeLegs.cellIso` owns the displayed pasting of the two naturality
isomorphisms with the selected comma comparison. `changeLegs.map₂` retains its
two endpoint cells literally. The only new deferred content is compatibility
of these explicit cells. `#print axioms` also reports `sorryAx` because the
ambient `PseudoComma` type carries the inherited
`ColaxComma.pseudoHomProperty.isMultiplicative` proof instance; it does not
select any of the displayed non-`Prop` data. -/

end PseudoComma

end Bicategory

end CategoryTheory
