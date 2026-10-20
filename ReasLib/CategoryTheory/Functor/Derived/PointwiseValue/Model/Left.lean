module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left-Derived Models and Pointwise Values

This file compares an arbitrary left-derived model with the concrete pointwise limit value.
The chosen total left-derived functor is only one specialization of this construction.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The canonical comparison from any left-derived model to the pointwise limit value. -/
@[stacks 05SA "left-derived model comparison with pointwise values"]
noncomputable def LeftDerived.Value.modelIso
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) (X : C) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] :
    LF.obj (S.Q.obj X) ≅ LeftDerived.Value.obj F S X :=
  ((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (F' := LF) (F := F) (L := S.Q) (α := α) (W := S)) (S.Q.obj X)).isoLimit

namespace LeftDerived.Value.modelIso

/-- At a localized object, a left-derived model is canonically compared with the pointwise
value at the selected source preimage. -/
@[stacks 05SA "left-derived model comparison at a localization object"]
noncomputable def objPreimage
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) (X : S.Localization) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] :
    LF.obj X ≅ LeftDerived.Value.obj F S (S.Q.objPreimage X) :=
  LF.mapIso (S.Q.objObjPreimageIso X).symm ≪≫
    LeftDerived.Value.modelIso F S LF α (S.Q.objPreimage X)

namespace objPreimage

/-- The forward arbitrary-object comparison first moves to the selected source preimage. -/
@[simp, stacks 05SA]
theorem hom
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) (X : S.Localization) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] :
    (LeftDerived.Value.modelIso.objPreimage F S LF α X).hom =
      LF.map (S.Q.objObjPreimageIso X).inv ≫
        (LeftDerived.Value.modelIso F S LF α (S.Q.objPreimage X)).hom := sorry

/-- The inverse arbitrary-object comparison returns from the selected source preimage. -/
@[simp, stacks 05SA]
theorem inv
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) (X : S.Localization) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] :
    (LeftDerived.Value.modelIso.objPreimage F S LF α X).inv =
      (LeftDerived.Value.modelIso F S LF α (S.Q.objPreimage X)).inv ≫
        LF.map (S.Q.objObjPreimageIso X).hom := sorry

end objPreimage

/-- Forward naturality of the comparison between a left-derived model and pointwise values. -/
@[reassoc (attr := simp), stacks 05SA]
theorem hom_naturality
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    LF.map (S.Q.map f) ≫ (LeftDerived.Value.modelIso F S LF α Y).hom =
      (LeftDerived.Value.modelIso F S LF α X).hom ≫
        LeftDerived.Value.map F S f := sorry

/-- Inverse naturality of the comparison between a left-derived model and pointwise values. -/
@[reassoc (attr := simp), stacks 05SA]
theorem inv_naturality
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    LeftDerived.Value.map F S f ≫
        (LeftDerived.Value.modelIso F S LF α Y).inv =
      (LeftDerived.Value.modelIso F S LF α X).inv ≫ LF.map (S.Q.map f) := sorry

/-- The model comparison is computed on every projection of the defining limit diagram. -/
@[reassoc (attr := simp), stacks 05SA]
theorem π
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S]
    (X : C) (U : StructuredArrow (S.Q.obj X) S.Q) :
    (LeftDerived.Value.modelIso F S LF α X).hom ≫
        limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) U =
      LF.map U.hom ≫ α.app U.right := sorry

/-- The model comparison identifies every denominator projection with the corresponding
localized map followed by the model counit. -/
@[reassoc (attr := simp), stacks 05SA]
theorem π_denominator
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S]
    {X X' : C} (s : X' ⟶ X) (hs : S s) :
    (LeftDerived.Value.modelIso F S LF α X).hom ≫
        LeftDerived.Value.π F S s hs =
      LF.map (Localization.isoOfHom S.Q S s hs).inv ≫ α.app X' := sorry

/-- For the identity denominator, the canonical pointwise projection is the model counit. -/
@[reassoc (attr := simp), stacks 05SA]
theorem counit
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S] [S.ContainsIdentities]
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.modelIso F S LF α X).hom ≫
        LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) = α.app X := sorry

end LeftDerived.Value.modelIso



end CategoryTheory.Functor
