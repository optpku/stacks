/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Biequivalence

/-!
# A chosen pseudoinverse of a biequivalence

This file constructs the object, `1`-morphism, and `2`-morphism action of a
chosen pseudoinverse. The construction first transports a morphism across the
chosen object equivalences and then applies the chosen inverse of the relevant
local equivalence.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Bicategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ChosenInverse

/-- The functor transporting a morphism across the chosen object
equivalences. -/
noncomputable def mapImage.transport (F : B ⥤ᵖ C) [F.IsBiequivalence]
    (X Y : C) :
    (X ⟶ Y) ⥤
      (F.obj (F.objPreimage X) ⟶ F.obj (F.objPreimage Y)) :=
  Bicategory.precomp Y (objPreimage.equivalence F X).hom ⋙
    Bicategory.postcomp (F.obj (F.objPreimage X))
      (objPreimage.equivalence F Y).inv

/-- The hom functor used by the chosen pseudoinverse of a biequivalence.

A morphism `f : X ⟶ Y` is first sent to
`e_X.hom ≫ f ≫ e_Y.inv`, where `e_X` and `e_Y` are the chosen object
equivalences, and is then lifted through the inverse of the local equivalence
induced by `F`. -/
noncomputable def homFunctor (F : B ⥤ᵖ C) [F.IsBiequivalence] (X Y : C) :
    (X ⟶ Y) ⥤ (F.objPreimage X ⟶ F.objPreimage Y) :=
  mapImage.transport F X Y ⋙
    (F.mapFunctor (F.objPreimage X) (F.objPreimage Y)).asEquivalence.inverse

/-- The transported identity isomorphism used by the identity comparison of
the chosen pseudoinverse. -/
noncomputable def transportedIdIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : C) :
    ((objPreimage.equivalence F X).hom ≫ 𝟙 X) ≫
        (objPreimage.equivalence F X).inv ≅
      F.map (𝟙 (F.objPreimage X)) :=
  Bicategory.whiskerRightIso
      (ρ_ (objPreimage.equivalence F X).hom)
      (objPreimage.equivalence F X).inv ≪≫
    (objPreimage.equivalence F X).unit.symm ≪≫
    (F.mapId (F.objPreimage X)).symm

/-- The identity comparison of the chosen pseudoinverse. -/
noncomputable def mapIdIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : C) :
    (homFunctor F X X).obj (𝟙 X) ≅ 𝟙 (F.objPreimage X) :=
  let E := (F.mapFunctor (F.objPreimage X) (F.objPreimage X)).asEquivalence
  E.inverse.mapIso (transportedIdIso F X) ≪≫
    E.unitIso.symm.app (𝟙 (F.objPreimage X))

/-- Transporting a composite across the chosen object equivalences agrees,
up to the middle counit, with composing the two separately transported
morphisms. -/
noncomputable def transportedCompIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((objPreimage.equivalence F X).hom ≫ (f ≫ g)) ≫
        (objPreimage.equivalence F Z).inv ≅
      (((objPreimage.equivalence F X).hom ≫ f) ≫
          (objPreimage.equivalence F Y).inv) ≫
        (((objPreimage.equivalence F Y).hom ≫ g) ≫
          (objPreimage.equivalence F Z).inv) :=
  Iso.refl _ ≪⊗≫
    Bicategory.whiskerRightIso
      (Bicategory.whiskerLeftIso
        ((objPreimage.equivalence F X).hom ≫ f)
        (objPreimage.equivalence F Y).counit.symm)
      (g ≫ (objPreimage.equivalence F Z).inv) ≪⊗≫
    Iso.refl _

/-- The image in `C` of the composition comparison for the chosen
pseudoinverse. -/
noncomputable def mappedCompIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((objPreimage.equivalence F X).hom ≫ (f ≫ g)) ≫
        (objPreimage.equivalence F Z).inv ≅
      F.map ((homFunctor F X Y).obj f ≫ (homFunctor F Y Z).obj g) :=
  let qf := ((objPreimage.equivalence F X).hom ≫ f) ≫
    (objPreimage.equivalence F Y).inv
  let qg := ((objPreimage.equivalence F Y).hom ≫ g) ≫
    (objPreimage.equivalence F Z).inv
  let Ef := (F.mapFunctor (F.objPreimage X) (F.objPreimage Y)).asEquivalence
  let Eg := (F.mapFunctor (F.objPreimage Y) (F.objPreimage Z)).asEquivalence
  transportedCompIso F f g ≪≫
    Bicategory.whiskerRightIso (Ef.counitIso.symm.app qf) qg ≪≫
    Bicategory.whiskerLeftIso (F.map ((homFunctor F X Y).obj f))
      (Eg.counitIso.symm.app qg) ≪≫
    (F.mapComp ((homFunctor F X Y).obj f)
      ((homFunctor F Y Z).obj g)).symm

/-- The composition comparison of the chosen pseudoinverse. -/
noncomputable def mapCompIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (homFunctor F X Z).obj (f ≫ g) ≅
      (homFunctor F X Y).obj f ≫ (homFunctor F Y Z).obj g :=
  let E := (F.mapFunctor (F.objPreimage X) (F.objPreimage Z)).asEquivalence
  E.inverse.mapIso (mappedCompIso F f g) ≪≫
    E.unitIso.symm.app
      ((homFunctor F X Y).obj f ≫ (homFunctor F Y Z).obj g)

end ChosenInverse

/-- A chosen pseudoinverse of a biequivalence.

Its object action is `F.objPreimage`; its local action is
`ChosenInverse.homFunctor`. All non-propositional comparison data are built
from the selected object equivalences and the chosen inverses of the local
equivalences. -/
noncomputable def chosenInverse (F : B ⥤ᵖ C) [F.IsBiequivalence] : C ⥤ᵖ B where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors F.objPreimage
    (ChosenInverse.homFunctor F)
  mapId := ChosenInverse.mapIdIso F
  mapComp := ChosenInverse.mapCompIso F
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

namespace ChosenInverse

/-- Mapping the chosen local inverse and then applying `F` is naturally
isomorphic to transport across the chosen object equivalences. -/
noncomputable def mapImage.natIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    (X Y : C) :
    homFunctor F X Y ⋙
        F.mapFunctor (F.objPreimage X) (F.objPreimage Y) ≅
      mapImage.transport F X Y :=
  let E := (F.mapFunctor (F.objPreimage X) (F.objPreimage Y)).asEquivalence
  E.congrRight.counitIso.app (mapImage.transport F X Y)

/-- Mapping a chosen inverse image through `F` recovers the morphism obtained
by transporting across the selected object equivalences. -/
noncomputable def mapImage.iso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y : C} (f : X ⟶ Y) :
    F.map (F.chosenInverse.map f) ≅
      ((objPreimage.equivalence F X).hom ≫ f) ≫
        (objPreimage.equivalence F Y).inv :=
  (mapImage.natIso F X Y).app f

end ChosenInverse

end CategoryTheory.Pseudofunctor
