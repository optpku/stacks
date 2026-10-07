module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Pseudofunctor.Basic

/-!
# Computations for changing pseudo comma legs

This leaf exposes the public computation interface of
`PseudoComma.changeLegs`. It keeps downstream arguments on the explicit
object, morphism, cell, and endpoint-comparison data without unfolding the
private pseudofunctor assembly.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace PseudoComma

variable {F F' : A ⥤ᵖ C} {G G' : B ⥤ᵖ C}

/-- The object action of `changeLegs` is its explicit changed-leg object. -/
@[simp]
theorem changeLegs.obj.action
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    (changeLegs α β).obj S = changeLegs.obj α β S := sorry

/-- The morphism action of `changeLegs` is its explicit changed-leg morphism. -/
@[simp]
theorem changeLegs.map.action
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    (changeLegs α β).map u = changeLegs.map α β u := sorry

/-- The `2`-morphism action of `changeLegs` is its explicit changed-leg cell. -/
@[simp]
theorem changeLegs.map₂.action
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v : S ⟶ T} (η : u ⟶ v) :
    (changeLegs α β).map₂ η = changeLegs.map₂ α β η := sorry

/-- The identity comparison of `changeLegs` is the changed-leg identity
comparison. -/
@[simp]
theorem changeLegs.mapId.action
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    (changeLegs α β).mapId S = changeLegs.mapId α β S := sorry

/-- The composition comparison of `changeLegs` is the changed-leg composition
comparison. -/
@[simp]
theorem changeLegs.mapComp.action
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    (changeLegs α β).mapComp u v = changeLegs.mapComp α β u v := sorry

/-- Changing pseudo comma legs commutes strictly with the left endpoint
projection. -/
theorem changeLegs.fst
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    (changeLegs α β).comp (fst F' G') = fst F G := sorry

/-- Changing pseudo comma legs commutes strictly with the right endpoint
projection. -/
theorem changeLegs.snd
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    (changeLegs α β).comp (snd F' G') = snd F G := sorry

/-- The forward identity comparison of changing pseudo comma legs is identity
on the left endpoint. -/
@[simp]
theorem changeLegs.mapId.hom.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    left₂ (F := F') (G := G') (changeLegs.mapId α β S).hom =
      𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The forward identity comparison of changing pseudo comma legs is identity
on the right endpoint. -/
@[simp]
theorem changeLegs.mapId.hom.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    right₂ (F := F') (G := G') (changeLegs.mapId α β S).hom =
      𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The inverse identity comparison of changing pseudo comma legs is identity
on the left endpoint. -/
@[simp]
theorem changeLegs.mapId.inv.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    left₂ (F := F') (G := G') (changeLegs.mapId α β S).inv =
      𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The inverse identity comparison of changing pseudo comma legs is identity
on the right endpoint. -/
@[simp]
theorem changeLegs.mapId.inv.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    right₂ (F := F') (G := G') (changeLegs.mapId α β S).inv =
      𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The forward composition comparison of changing pseudo comma legs is
identity on the left endpoint. -/
@[simp]
theorem changeLegs.mapComp.hom.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    left₂ (F := F') (G := G') (changeLegs.mapComp α β u v).hom =
      𝟙 (left (F := F) (G := G) u ≫ left (F := F) (G := G) v) := sorry

/-- The forward composition comparison of changing pseudo comma legs is
identity on the right endpoint. -/
@[simp]
theorem changeLegs.mapComp.hom.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    right₂ (F := F') (G := G') (changeLegs.mapComp α β u v).hom =
      𝟙 (right (F := F) (G := G) u ≫ right (F := F) (G := G) v) := sorry

/-- The inverse composition comparison of changing pseudo comma legs is
identity on the left endpoint. -/
@[simp]
theorem changeLegs.mapComp.inv.left
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    left₂ (F := F') (G := G') (changeLegs.mapComp α β u v).inv =
      𝟙 (left (F := F) (G := G) u ≫ left (F := F) (G := G) v) := sorry

/-- The inverse composition comparison of changing pseudo comma legs is
identity on the right endpoint. -/
@[simp]
theorem changeLegs.mapComp.inv.right
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    right₂ (F := F') (G := G') (changeLegs.mapComp α β u v).inv =
      𝟙 (right (F := F) (G := G) u ≫ right (F := F) (G := G) v) := sorry

end PseudoComma

end Bicategory

end CategoryTheory
