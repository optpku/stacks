/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Whiskering

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.SmallToBig

variable {S T : Scheme.{u}}

/-- The pullback projection maps relocalized base changes to their original objects. -/
private def pullbackRelocalizationToIdentity (f : T ⟶ S) :
    smallZariskiPullback f ⋙ relocalizationFunctor f ⟶ relocalizationFunctor (𝟙 S) :=
  (Functor.associator (smallZariskiPullback f)
    (MorphismProperty.Over.forget @IsOpenImmersion ⊤ T) (Over.map f)).inv ≫
    whiskerRight (MorphismProperty.Over.pullbackCompForgetIso
      (P := @IsOpenImmersion) (Q := ⊤) f).hom (Over.map f) ≫
    (Functor.associator (MorphismProperty.Over.forget @IsOpenImmersion ⊤ S)
      (Over.pullback f) (Over.map f)).hom ≫
    whiskerLeft (MorphismProperty.Over.forget @IsOpenImmersion ⊤ S)
      (Over.mapPullbackAdj f).counit ≫
    whiskerLeft (MorphismProperty.Over.forget @IsOpenImmersion ⊤ S) (Over.mapId S).inv

/-- Restriction to the small site maps naturally to restriction after base change. -/
private def restrictionComparison (f : T ⟶ S) :
    (siteMorphismOfTopoi S).pushforward ⟶ inverseImage f ⋙ (smallMorphism f).pushforward :=
  @Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
      (pullbackRelocalizationToIdentity f) (Type (u + 1)) _
      S.smallZariskiTopology S.bigZariskiTopology
      (Functor.isContinuous_comp (smallZariskiPullback f) (relocalizationFunctor f)
        S.smallZariskiTopology T.smallZariskiTopology S.bigZariskiTopology) inferInstance ≫
    (Functor.sheafPushforwardContinuousComp (smallZariskiPullback f)
      (relocalizationFunctor f) (Type (u + 1))
      S.smallZariskiTopology T.smallZariskiTopology S.bigZariskiTopology).inv

/-- Small-site inverse image maps naturally to restriction of big-site inverse image. -/
private def inverseImageComparison (f : T ⟶ S) :
    (smallMorphism f)⁻¹ ⟶ (siteMorphismOfTopoi S)⁻¹ ⋙ inverseImage f :=
  (((smallMorphism f).adjunction.whiskerRight
    (Sheaf S.smallZariskiTopology (Type (u + 1)))).homEquiv
      (𝟭 _) ((siteMorphismOfTopoi S)⁻¹ ⋙ inverseImage f)).symm
    ((siteMorphismOfTopoi S).adjunction.unit ≫
      whiskerLeft ((siteMorphismOfTopoi S)⁻¹) (restrictionComparison f) ≫
      (Functor.associator ((siteMorphismOfTopoi S)⁻¹)
        (inverseImage f) (smallMorphism f).pushforward).inv)

/-- Global sections of small-site pullback map canonically to big-site inverse-image sections. -/
@[no_expose]
def sectionsComparison (f : T ⟶ S)
    (F : Sheaf S.smallZariskiTopology (Type (u + 1))) :
    (((smallMorphism f)⁻¹).obj F).1.obj
        (op (MorphismProperty.Over.mk _ (𝟙 T) inferInstance)) →
      (((siteMorphismOfTopoi S)⁻¹).obj F).1.obj (op (Over.mk f)) :=
  fun sectionValue =>
    (((siteMorphismOfTopoi S)⁻¹).obj F).1.map
      ((Over.isoMk (Iso.refl T) rfl :
        (relocalizationFunctor f).obj (MorphismProperty.Over.mk _ (𝟙 T) inferInstance) ≅
          Over.mk f).inv.op)
      ((inverseImage_objObjIso f (((siteMorphismOfTopoi S)⁻¹).obj F)
        (MorphismProperty.Over.mk _ (𝟙 T) inferInstance)).hom
        (((inverseImageComparison f).app F).hom.app
          (op (MorphismProperty.Over.mk _ (𝟙 T) inferInstance)) sectionValue))

/-- The canonical comparison identifies small-site global sections with big-site sections. -/
theorem sectionsComparison_bijective (f : T ⟶ S)
    (F : Sheaf S.smallZariskiTopology (Type (u + 1))) :
    Function.Bijective (sectionsComparison f F) := sorry

/-- Small-to-big inverse image of a Zariski sheaf satisfies fpqc descent. -/
theorem inverseImage_isSheaf_fpqc (S : Scheme.{u})
    (F : Sheaf S.smallZariskiTopology (Type (u + 1))) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (((siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

end AlgebraicGeometry.Scheme.Zariski.SmallToBig
