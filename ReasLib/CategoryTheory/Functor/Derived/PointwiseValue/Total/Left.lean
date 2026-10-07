module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Left-Derived Functors and Pointwise Values

This file compares the chosen total left-derived functor with its concrete pointwise limit
values.  It exposes both arbitrary structured-arrow legs and denominator specializations.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The canonical comparison between the total left-derived functor at `S.Q.obj X` and its
pointwise limit presentation at `X`. -/
@[stacks 05SA]
noncomputable def LeftDerived.Value.totalIso
    (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    [F.HasPointwiseLeftDerivedFunctor S] :
    (F.totalLeftDerived S.Q S).obj (S.Q.obj X) ≅ LeftDerived.Value.obj F S X :=
  LeftDerived.Value.modelIso F S (F.totalLeftDerived S.Q S)
    (F.totalLeftDerivedCounit S.Q S) X

/-- At an arbitrary localized object, the total left-derived value is canonically isomorphic
to the pointwise value at the selected source preimage. -/
@[stacks 05SA]
noncomputable def LeftDerived.Value.totalIso.objPreimage
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseLeftDerivedFunctor S] :
    (F.totalLeftDerived S.Q S).obj X ≅ LeftDerived.Value.obj F S (S.Q.objPreimage X) :=
  LeftDerived.Value.modelIso.objPreimage F S (F.totalLeftDerived S.Q S)
    (F.totalLeftDerivedCounit S.Q S) X

namespace LeftDerived.Value.totalIso.objPreimage

/-- The forward map of the arbitrary-object comparison first moves to the selected source
preimage and then applies the pointwise comparison. -/
@[simp, stacks 05SA]
theorem hom
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseLeftDerivedFunctor S] :
    (LeftDerived.Value.totalIso.objPreimage F S X).hom =
      (F.totalLeftDerived S.Q S).map (S.Q.objObjPreimageIso X).inv ≫
        (LeftDerived.Value.totalIso F S (S.Q.objPreimage X)).hom := sorry

/-- The inverse map of the arbitrary-object comparison first applies the inverse pointwise
comparison and then returns from the selected source preimage. -/
@[simp, stacks 05SA]
theorem inv
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseLeftDerivedFunctor S] :
    (LeftDerived.Value.totalIso.objPreimage F S X).inv =
      (LeftDerived.Value.totalIso F S (S.Q.objPreimage X)).inv ≫
        (F.totalLeftDerived S.Q S).map (S.Q.objObjPreimageIso X).hom := sorry

end LeftDerived.Value.totalIso.objPreimage

/-- The total left-derived comparison is natural in the object of the source category. -/
@[reassoc (attr := simp), stacks 05SA]
theorem LeftDerived.Value.totalIso.hom_naturality
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseLeftDerivedFunctor S]
    {X Y : C} (f : X ⟶ Y) :
    (F.totalLeftDerived S.Q S).map (S.Q.map f) ≫
        (LeftDerived.Value.totalIso F S Y).hom =
      (LeftDerived.Value.totalIso F S X).hom ≫ LeftDerived.Value.map F S f := sorry

/-- Naturality of the inverse total-to-pointwise left-derived comparison. -/
@[reassoc (attr := simp), stacks 05SA]
theorem LeftDerived.Value.totalIso.inv_naturality
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseLeftDerivedFunctor S]
    {X Y : C} (f : X ⟶ Y) :
    LeftDerived.Value.map F S f ≫
        (LeftDerived.Value.totalIso F S Y).inv =
      (LeftDerived.Value.totalIso F S X).inv ≫
        (F.totalLeftDerived S.Q S).map (S.Q.map f) := sorry

/-- The total left-derived comparison is computed on every leg of the structured-arrow diagram
by the image of the leg followed by the total counit. -/
@[reassoc (attr := simp), stacks 05SA]
theorem LeftDerived.Value.totalIso.π
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseLeftDerivedFunctor S]
    (X : C) (U : StructuredArrow (S.Q.obj X) S.Q) :
    (LeftDerived.Value.totalIso F S X).hom ≫
        limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) U =
      (F.totalLeftDerived S.Q S).map U.hom ≫
        (F.totalLeftDerivedCounit S.Q S).app U.right := sorry

/-- The total left-derived comparison identifies the limit projection associated to any
denominator with the corresponding localized leg followed by the total counit. -/
@[reassoc (attr := simp), stacks 05SA]
theorem LeftDerived.Value.totalIso.π_denominator
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseLeftDerivedFunctor S]
    {X X' : C} (s : X' ⟶ X) (hs : S s) :
    (LeftDerived.Value.totalIso F S X).hom ≫ LeftDerived.Value.π F S s hs =
      (F.totalLeftDerived S.Q S).map (Localization.isoOfHom S.Q S s hs).inv ≫
        (F.totalLeftDerivedCounit S.Q S).app X' := sorry

/-- The pointwise identity-denominator projection becomes the total left-derived counit under
the value comparison. -/
@[reassoc (attr := simp), stacks 05SA]
theorem LeftDerived.Value.totalIso.counit
    (F : C ⥤ D) (S : MorphismProperty C) [S.ContainsIdentities]
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.totalIso F S X).hom ≫
        LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) =
      (F.totalLeftDerivedCounit S.Q S).app X := sorry



end CategoryTheory.Functor
