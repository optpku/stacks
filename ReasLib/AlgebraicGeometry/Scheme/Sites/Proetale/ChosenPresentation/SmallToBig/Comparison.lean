/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Identity
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# Small and big pro-étale geometric morphisms

Base change on chosen small pro-étale sites induces a geometric morphism.
Its comparison with big-slice base change and relocalization is given by
canonical natural isomorphisms.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier}

/-- The geometric morphism induced by base change on chosen small pro-étale sites. -/
def smallMorphism (f : T ⟶ S) [UnivLE.{max u v, w}]
    [HasWeakSheafify (smallTopology X T) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, u, u, w}
      (smallTopology X S) (smallTopology X T) :=
  @IsMorphismOfSites.toMorphismOfTopoiIn _ _ _ _ _ _ (smallPullback f)
    (smallPullback_isMorphismOfSites f) inferInstance
    (smallPullback_op_hasLeftKanExtension f)
    (smallPullback_sheafPullback_preservesFiniteLimits f)

/-- Direct image along small-site base change evaluates on the base-changed object. -/
theorem smallMorphism_pushforward_obj_obj (f : T ⟶ S) [UnivLE.{max u v, w}]
    [HasWeakSheafify (smallTopology X T) (Type w)]
    (F : Sheaf (smallTopology X T) (Type w)) (U : smallSite X S) :
    ((smallMorphism f).pushforward.obj F).1.obj (op U) =
      F.1.obj (op ((smallPullback f).obj U)) := rfl

/-- Relocalization factors through big-slice base change on inverse images. -/
def morphism_comp_big_inverseImageIso (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)] :
    (morphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp (Big.morphismOfTopoi f)
        (morphismOfTopoi (𝟙 T))).inverseImage :=
  (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Functor.isoWhiskerRight (relocalizationFunctor_id_iso X T) (Big.map f))
    (Type w) _ (smallTopology X T) (bigTopology X T) (bigTopology X S)
    (relocalizationFunctor_isContinuous (𝟙 T)) (Big.map_isContinuous f)
    (relocalizationFunctor_isContinuous f)).symm

/-- Small-site base change commutes with the inclusions into the big slices. -/
def smallPullback_comp_relocalization_id_iso (f : T ⟶ S) :
    smallPullback f ⋙ relocalizationFunctor (𝟙 T) ≅
      relocalizationFunctor (𝟙 S) ⋙ Big.pullback f :=
  Functor.isoWhiskerLeft (smallPullback f) (relocalizationFunctor_id_iso X T) ≪≫
    smallPullback_comp_smallInclusion f ≪≫
      Functor.isoWhiskerRight (relocalizationFunctor_id_iso X S).symm (Big.pullback f)

/-- The small/big pro-étale square commutes on direct images. -/
def smallMorphism_comp_site_pushforwardIso (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasWeakSheafify (bigTopology X T) (Type w)] :
    (MorphismOfTopoiIn.comp (smallMorphism f) (siteMorphismOfTopoi X T)).pushforward ≅
      (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S)
        (Big.morphismOfTopoi f)).pushforward :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (smallPullback_comp_relocalization_id_iso f) (Type w) _
    (smallTopology X S) (smallTopology X T) (bigTopology X T)
    (smallPullback_isContinuous f) (relocalizationFunctor_isContinuous (𝟙 T))
    (@Functor.isContinuous_comp _ _ _ _ _ _
      (relocalizationFunctor (𝟙 S)) (Big.pullback f)
      (smallTopology X S) (bigTopology X S) (bigTopology X T)
      (relocalizationFunctor_isContinuous (𝟙 S)) (Big.pullback_isContinuous f)) ≪≫
    (@Functor.sheafPushforwardContinuousComp _ _ _ _ _ _
      (relocalizationFunctor (𝟙 S)) (Big.pullback f) (Type w) _
      (smallTopology X S) (bigTopology X S) (bigTopology X T)
      (relocalizationFunctor_isContinuous (𝟙 S)) (Big.pullback_isContinuous f)).symm

/-- The inverse image of small-site base change factors through the big slices. -/
def smallMorphism_comp_big_inverseImageIso (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    (smallMorphism f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S) (Big.morphismOfTopoi f))
        (morphismOfTopoi (𝟙 T))).inverseImage :=
  let square := Adjunction.leftAdjointUniq
    (((MorphismOfTopoiIn.comp (smallMorphism f) (siteMorphismOfTopoi X T)).adjunction).ofNatIsoRight
      (smallMorphism_comp_site_pushforwardIso f))
    ((MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S) (Big.morphismOfTopoi f)).adjunction)
  (Functor.rightUnitor (smallMorphism f).inverseImage).symm ≪≫
    Functor.isoWhiskerLeft (smallMorphism f).inverseImage
      (siteMorphismOfTopoi_comp_morphismOfTopoi_id_iso X T).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight square (morphismOfTopoi (𝟙 T)).inverseImage

/-- The inverse image of small-site base change factors through relocalization. -/
def smallMorphism_comp_inverseImageIso (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    (smallMorphism f).inverseImage ≅
      (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S)
        (morphismOfTopoi f)).inverseImage :=
  smallMorphism_comp_big_inverseImageIso f ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (siteMorphismOfTopoi X S).inverseImage
      (morphism_comp_big_inverseImageIso f).symm

end AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig
