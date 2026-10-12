/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Computations
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans

/-!
# Changing the common target pseudofunctor of a pseudo comma bicategory

A change of common target diagram requires an equivalence, rather than merely
a strong transformation: the left pseudo comma leg is contravariant while the
right leg is covariant. This leaf specializes `PseudoComma.changeLegs` to that
frequent situation.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

namespace PseudoComma

variable {H K : C ⥤ᵖ D}

/-- Transport a pseudo comma bicategory along an equivalence of its common
target pseudofunctor.

For `e : H ≌ K`, the left leg uses `e.inv.precomp F` and the right leg uses
`e.hom.precomp G`. An arbitrary strong transformation `H ⟶ K` is insufficient:
the structural arrow must be transported contravariantly at its source and
covariantly at its target. -/
noncomputable def changeTarget
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K) :
    Pseudofunctor (PseudoComma (F.comp H) (G.comp H))
      (PseudoComma (F.comp K) (G.comp K)) :=
  changeLegs (e.inv.precomp F) (e.hom.precomp G)

/-- `changeTarget` is the generic change-of-legs action with the inverse
precomposed equivalence on the left and the forward precomposed equivalence on
the right. -/
@[simp]
theorem changeTarget.eqChangeLegs
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K) :
    changeTarget F G e =
      changeLegs (e.inv.precomp F) (e.hom.precomp G) := sorry

/-- The object action of `changeTarget` is the explicit generic changed-leg
object. -/
@[simp]
theorem changeTarget.obj.action
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    (changeTarget F G e).obj S =
      changeLegs.obj (e.inv.precomp F) (e.hom.precomp G) S := sorry

/-- The morphism action of `changeTarget` is the explicit generic changed-leg
morphism. -/
@[simp]
theorem changeTarget.map.action
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)} (u : S ⟶ T) :
    (changeTarget F G e).map u =
      changeLegs.map (e.inv.precomp F) (e.hom.precomp G) u := sorry

/-- The `2`-morphism action of `changeTarget` is the explicit generic
changed-leg cell. -/
@[simp]
theorem changeTarget.map₂.action
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)}
    {u v : S ⟶ T} (η : u ⟶ v) :
    (changeTarget F G e).map₂ η =
      changeLegs.map₂ (e.inv.precomp F) (e.hom.precomp G) η := sorry

/-- The identity comparison of `changeTarget` is the generic changed-leg
identity comparison. -/
@[simp]
theorem changeTarget.mapId.action
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    (changeTarget F G e).mapId S =
      changeLegs.mapId (e.inv.precomp F) (e.hom.precomp G) S := sorry

/-- The composition comparison of `changeTarget` is the generic changed-leg
composition comparison. -/
@[simp]
theorem changeTarget.mapComp.action
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T U : PseudoComma (F.comp H) (G.comp H)}
    (u : S ⟶ T) (v : T ⟶ U) :
    (changeTarget F G e).mapComp u v =
      changeLegs.mapComp (e.inv.precomp F) (e.hom.precomp G) u v := sorry

/-- Changing the common target pseudofunctor preserves the left endpoint
object. -/
@[simp]
theorem changeTarget.obj.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    ColaxComma.left ((changeTarget F G e).obj S) = ColaxComma.left S := sorry

/-- Changing the common target pseudofunctor preserves the right endpoint
object. -/
@[simp]
theorem changeTarget.obj.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    ColaxComma.right ((changeTarget F G e).obj S) = ColaxComma.right S := sorry

/-- The structural arrow after changing the common target pseudofunctor is
the inverse left component, original structural arrow, and forward right
component composite. -/
@[simp]
theorem changeTarget.obj.hom
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    ColaxComma.hom ((changeTarget F G e).obj S) =
      (e.inv.precomp F).app (ColaxComma.left S) ≫ ColaxComma.hom S ≫
        (e.hom.precomp G).app (ColaxComma.right S) := sorry

/-- Changing the common target pseudofunctor preserves the left endpoint map. -/
@[simp]
theorem changeTarget.map.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)} (u : S ⟶ T) :
    left ((changeTarget F G e).map u) = left u := sorry

/-- Changing the common target pseudofunctor preserves the right endpoint map. -/
@[simp]
theorem changeTarget.map.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)} (u : S ⟶ T) :
    right ((changeTarget F G e).map u) = right u := sorry

/-- The selected comparison of a morphism transported by `changeTarget` is the
canonical pasted change-of-legs comparison. -/
@[simp]
theorem changeTarget.map.cellIso
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)} (u : S ⟶ T) :
    PseudoComma.cellIso (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).map u) =
      changeLegs.cellIso (e.inv.precomp F) (e.hom.precomp G) u := sorry

/-- The structural cell of a morphism transported by `changeTarget` is the
forward cell of its canonical pasted comparison. -/
@[simp]
theorem changeTarget.map.cell
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)} (u : S ⟶ T) :
    PseudoComma.cell (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).map u) =
      (changeLegs.cellIso (e.inv.precomp F) (e.hom.precomp G) u).hom := sorry

/-- Changing the common target preserves the left endpoint `2`-cell. -/
@[simp]
theorem changeTarget.map₂.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)}
    {u v : S ⟶ T} (η : u ⟶ v) :
    left₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).map₂ η) =
      left₂ (F := F.comp H) (G := G.comp H) η := sorry

/-- Changing the common target preserves the right endpoint `2`-cell. -/
@[simp]
theorem changeTarget.map₂.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T : PseudoComma (F.comp H) (G.comp H)}
    {u v : S ⟶ T} (η : u ⟶ v) :
    right₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).map₂ η) =
      right₂ (F := F.comp H) (G := G.comp H) η := sorry

/-- The forward identity comparison of `changeTarget` is identity on the left
endpoint. -/
@[simp]
theorem changeTarget.mapId.hom.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    left₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapId S).hom =
      𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The forward identity comparison of `changeTarget` is identity on the right
endpoint. -/
@[simp]
theorem changeTarget.mapId.hom.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    right₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapId S).hom =
      𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The inverse identity comparison of `changeTarget` is identity on the left
endpoint. -/
@[simp]
theorem changeTarget.mapId.inv.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    left₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapId S).inv =
      𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The inverse identity comparison of `changeTarget` is identity on the right
endpoint. -/
@[simp]
theorem changeTarget.mapId.inv.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    (S : PseudoComma (F.comp H) (G.comp H)) :
    right₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapId S).inv =
      𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The forward composition comparison of `changeTarget` is identity on the
left endpoint. -/
@[simp]
theorem changeTarget.mapComp.hom.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T U : PseudoComma (F.comp H) (G.comp H)}
    (u : S ⟶ T) (v : T ⟶ U) :
    left₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapComp u v).hom =
      𝟙 (left (F := F.comp H) (G := G.comp H) u ≫
        left (F := F.comp H) (G := G.comp H) v) := sorry

/-- The forward composition comparison of `changeTarget` is identity on the
right endpoint. -/
@[simp]
theorem changeTarget.mapComp.hom.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T U : PseudoComma (F.comp H) (G.comp H)}
    (u : S ⟶ T) (v : T ⟶ U) :
    right₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapComp u v).hom =
      𝟙 (right (F := F.comp H) (G := G.comp H) u ≫
        right (F := F.comp H) (G := G.comp H) v) := sorry

/-- The inverse composition comparison of `changeTarget` is identity on the
left endpoint. -/
@[simp]
theorem changeTarget.mapComp.inv.left
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T U : PseudoComma (F.comp H) (G.comp H)}
    (u : S ⟶ T) (v : T ⟶ U) :
    left₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapComp u v).inv =
      𝟙 (left (F := F.comp H) (G := G.comp H) u ≫
        left (F := F.comp H) (G := G.comp H) v) := sorry

/-- The inverse composition comparison of `changeTarget` is identity on the
right endpoint. -/
@[simp]
theorem changeTarget.mapComp.inv.right
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K)
    {S T U : PseudoComma (F.comp H) (G.comp H)}
    (u : S ⟶ T) (v : T ⟶ U) :
    right₂ (F := F.comp K) (G := G.comp K)
        ((changeTarget F G e).mapComp u v).inv =
      𝟙 (right (F := F.comp H) (G := G.comp H) u ≫
        right (F := F.comp H) (G := G.comp H) v) := sorry

/-- `changeTarget` commutes strictly with the left endpoint projection. -/
theorem changeTarget.fst
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K) :
    (changeTarget F G e).comp (fst (F.comp K) (G.comp K)) =
      fst (F.comp H) (G.comp H) := sorry

/-- `changeTarget` commutes strictly with the right endpoint projection. -/
theorem changeTarget.snd
    (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) (e : H ≌ K) :
    (changeTarget F G e).comp (snd (F.comp K) (G.comp K)) =
      snd (F.comp H) (G.comp H) := sorry

end PseudoComma

end Bicategory

end CategoryTheory
