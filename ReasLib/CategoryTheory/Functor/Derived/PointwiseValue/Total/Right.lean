/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Right-Derived Functors and Pointwise Values

This file compares the chosen total right-derived functor with its concrete pointwise colimit
values.  It exposes both arbitrary costructured-arrow legs and denominator specializations.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The canonical comparison between the total right-derived functor at `S.Q.obj X` and its
pointwise colimit presentation at `X`. -/
@[stacks 05SA]
noncomputable def RightDerived.Value.totalIso
    (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    [F.HasPointwiseRightDerivedFunctor S] :
    (F.totalRightDerived S.Q S).obj (S.Q.obj X) ≅ RightDerived.Value.obj F S X :=
  RightDerived.Value.modelIso F S (F.totalRightDerived S.Q S)
    (F.totalRightDerivedUnit S.Q S) X

/-- At an arbitrary localized object, the total right-derived value is canonically isomorphic
to the pointwise value at the selected source preimage. -/
@[stacks 05SA]
noncomputable def RightDerived.Value.totalIso.objPreimage
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseRightDerivedFunctor S] :
    (F.totalRightDerived S.Q S).obj X ≅ RightDerived.Value.obj F S (S.Q.objPreimage X) :=
  RightDerived.Value.modelIso.objPreimage F S (F.totalRightDerived S.Q S)
    (F.totalRightDerivedUnit S.Q S) X

namespace RightDerived.Value.totalIso.objPreimage

/-- The forward map of the arbitrary-object comparison first moves to the selected source
preimage and then applies the pointwise comparison. -/
@[simp, stacks 05SA]
theorem hom
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseRightDerivedFunctor S] :
    (RightDerived.Value.totalIso.objPreimage F S X).hom =
      (F.totalRightDerived S.Q S).map (S.Q.objObjPreimageIso X).inv ≫
        (RightDerived.Value.totalIso F S (S.Q.objPreimage X)).hom := sorry

/-- The inverse map of the arbitrary-object comparison first applies the inverse pointwise
comparison and then returns from the selected source preimage. -/
@[simp, stacks 05SA]
theorem inv
    (F : C ⥤ D) (S : MorphismProperty C) (X : S.Localization)
    [F.HasPointwiseRightDerivedFunctor S] :
    (RightDerived.Value.totalIso.objPreimage F S X).inv =
      (RightDerived.Value.totalIso F S (S.Q.objPreimage X)).inv ≫
        (F.totalRightDerived S.Q S).map (S.Q.objObjPreimageIso X).hom := sorry

end RightDerived.Value.totalIso.objPreimage

/-- The total right-derived comparison is natural in the object of the source category. -/
@[reassoc (attr := simp), stacks 05SA]
theorem RightDerived.Value.totalIso.hom_naturality
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseRightDerivedFunctor S]
    {X Y : C} (f : X ⟶ Y) :
    (F.totalRightDerived S.Q S).map (S.Q.map f) ≫
        (RightDerived.Value.totalIso F S Y).hom =
      (RightDerived.Value.totalIso F S X).hom ≫ RightDerived.Value.map F S f := sorry

/-- Naturality of the inverse total-to-pointwise right-derived comparison. -/
@[reassoc (attr := simp), stacks 05SA]
theorem RightDerived.Value.totalIso.inv_naturality
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseRightDerivedFunctor S]
    {X Y : C} (f : X ⟶ Y) :
    RightDerived.Value.map F S f ≫
        (RightDerived.Value.totalIso F S Y).inv =
      (RightDerived.Value.totalIso F S X).inv ≫
        (F.totalRightDerived S.Q S).map (S.Q.map f) := sorry

/-- The total right-derived comparison is computed on every leg of the costructured-arrow
diagram by the total unit followed by the image of the leg. -/
@[reassoc (attr := simp), stacks 05SA]
theorem RightDerived.Value.totalIso.ι
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseRightDerivedFunctor S]
    (X : C) (U : CostructuredArrow S.Q (S.Q.obj X)) :
    (F.totalRightDerivedUnit S.Q S).app U.left ≫
        (F.totalRightDerived S.Q S).map U.hom ≫
      (RightDerived.Value.totalIso F S X).hom =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) U := sorry

/-- The total right-derived comparison identifies the canonical localized leg associated to any
denominator with the corresponding colimit leg of the pointwise value. -/
@[reassoc (attr := simp), stacks 05SA]
theorem RightDerived.Value.totalIso.ι_denominator
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseRightDerivedFunctor S]
    {X X' : C} (s : X ⟶ X') (hs : S s) :
    (F.totalRightDerivedUnit S.Q S).app X' ≫
        (F.totalRightDerived S.Q S).map (Localization.isoOfHom S.Q S s hs).inv ≫
      (RightDerived.Value.totalIso F S X).hom = RightDerived.Value.ι F S s hs := sorry

/-- The total right-derived unit becomes the identity-denominator leg under the pointwise value
comparison. -/
@[reassoc (attr := simp), stacks 05SA]
theorem RightDerived.Value.totalIso.unit
    (F : C ⥤ D) (S : MorphismProperty C) [S.ContainsIdentities]
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    (F.totalRightDerivedUnit S.Q S).app X ≫
        (RightDerived.Value.totalIso F S X).hom =
      RightDerived.Value.ι F S (𝟙 X) (S.id_mem X) := sorry



end CategoryTheory.Functor
