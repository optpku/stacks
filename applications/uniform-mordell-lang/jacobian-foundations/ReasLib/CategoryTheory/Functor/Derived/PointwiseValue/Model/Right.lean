module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Right-Derived Models and Pointwise Values

This file compares an arbitrary right-derived model with the concrete pointwise colimit value.
The chosen total right-derived functor is only one specialization of this construction.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The canonical comparison from any right-derived model to the pointwise colimit value. -/
@[stacks 05SA "right-derived model comparison with pointwise values"]
noncomputable def RightDerived.Value.modelIso
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) (X : C) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] :
    RF.obj (S.Q.obj X) ≅ RightDerived.Value.obj F S X :=
  ((isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
      (F' := RF) (F := F) (L := S.Q) (α := α) (W := S)) (S.Q.obj X)).isoColimit

namespace RightDerived.Value.modelIso

/-- At a localized object, a right-derived model is canonically compared with the pointwise
value at the selected source preimage. -/
@[stacks 05SA "right-derived model comparison at a localization object"]
noncomputable def objPreimage
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) (X : S.Localization) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] :
    RF.obj X ≅ RightDerived.Value.obj F S (S.Q.objPreimage X) :=
  RF.mapIso (S.Q.objObjPreimageIso X).symm ≪≫
    RightDerived.Value.modelIso F S RF α (S.Q.objPreimage X)

namespace objPreimage

/-- The forward arbitrary-object comparison first moves to the selected source preimage. -/
@[simp, stacks 05SA]
theorem hom
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) (X : S.Localization) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] :
    (RightDerived.Value.modelIso.objPreimage F S RF α X).hom =
      RF.map (S.Q.objObjPreimageIso X).inv ≫
        (RightDerived.Value.modelIso F S RF α (S.Q.objPreimage X)).hom := sorry

/-- The inverse arbitrary-object comparison returns from the selected source preimage. -/
@[simp, stacks 05SA]
theorem inv
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) (X : S.Localization) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] :
    (RightDerived.Value.modelIso.objPreimage F S RF α X).inv =
      (RightDerived.Value.modelIso F S RF α (S.Q.objPreimage X)).inv ≫
        RF.map (S.Q.objObjPreimageIso X).hom := sorry

end objPreimage

/-- Forward naturality of the comparison between a right-derived model and pointwise values. -/
@[reassoc (attr := simp), stacks 05SA]
theorem hom_naturality
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    RF.map (S.Q.map f) ≫ (RightDerived.Value.modelIso F S RF α Y).hom =
      (RightDerived.Value.modelIso F S RF α X).hom ≫
        RightDerived.Value.map F S f := sorry

/-- Inverse naturality of the comparison between a right-derived model and pointwise values. -/
@[reassoc (attr := simp), stacks 05SA]
theorem inv_naturality
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    RightDerived.Value.map F S f ≫
        (RightDerived.Value.modelIso F S RF α Y).inv =
      (RightDerived.Value.modelIso F S RF α X).inv ≫ RF.map (S.Q.map f) := sorry

/-- The model comparison is computed on every leg of the defining colimit diagram. -/
@[reassoc (attr := simp), stacks 05SA]
theorem ι
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S]
    (X : C) (U : CostructuredArrow S.Q (S.Q.obj X)) :
    α.app U.left ≫ RF.map U.hom ≫
        (RightDerived.Value.modelIso F S RF α X).hom =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) U := sorry

/-- The model comparison identifies every denominator leg with the corresponding colimit leg. -/
@[reassoc (attr := simp), stacks 05SA]
theorem ι_denominator
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S]
    {X X' : C} (s : X ⟶ X') (hs : S s) :
    α.app X' ≫ RF.map (Localization.isoOfHom S.Q S s hs).inv ≫
        (RightDerived.Value.modelIso F S RF α X).hom =
      RightDerived.Value.ι F S s hs := sorry

/-- For the identity denominator, the model unit is the canonical pointwise colimit leg. -/
@[reassoc (attr := simp), stacks 05SA]
theorem unit
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S] [S.ContainsIdentities]
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    α.app X ≫ (RightDerived.Value.modelIso F S RF α X).hom =
      RightDerived.Value.ι F S (𝟙 X) (S.id_mem X) := sorry

end RightDerived.Value.modelIso



end CategoryTheory.Functor
