module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Comparison

/-!
# Composition on chosen pro-étale sites

Base change along composable morphisms induces canonical composition
isomorphisms on the big and small pro-étale topoi.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {R S T : X.carrier}
  (f : R ⟶ S) (g : S ⟶ T)

/-- Big pro-étale inverse images compose canonically along composable morphisms. -/
def Big.morphismOfTopoi_comp_inverseImageIso :
    (MorphismOfTopoiIn.comp (Big.morphismOfTopoi g)
      (Big.morphismOfTopoi f)).inverseImage ≅
        (Big.morphismOfTopoi (f ≫ g)).inverseImage :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Over.mapComp f g).symm (Type w) _
    (bigTopology X R) (bigTopology X S) (bigTopology X T)
    (Big.map_isContinuous f) (Big.map_isContinuous g)
    (Big.map_isContinuous (f ≫ g))

/-- Iterated base change on chosen small pro-étale sites is canonically
isomorphic to base change along the composite. -/
def smallPullbackCompIso :
    smallPullback g ⋙ smallPullback f ≅ smallPullback (f ≫ g) :=
  let bigComp : Big.pullback g ⋙ Big.pullback f ≅ Big.pullback (f ≫ g) :=
    Adjunction.rightAdjointUniq
      (((Big.mapPullbackAdjunction f).comp (Big.mapPullbackAdjunction g)).ofNatIsoLeft
        (Over.mapComp f g).symm)
      (Big.mapPullbackAdjunction (f ≫ g))
  @Functor.fullyFaithfulCancelRight _ _ _ _ _ _ _ _ (smallInclusion X R)
    (smallObjects X R).fullyFaithfulι.full (smallObjects X R).fullyFaithfulι.faithful
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (smallPullback g) (smallPullback_comp_smallInclusion f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallPullback_comp_smallInclusion g) (Big.pullback f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (smallInclusion X T) bigComp ≪≫
      (smallPullback_comp_smallInclusion (f ≫ g)).symm)

namespace SmallToBig

variable [UnivLE.{max u v, w}]
  [HasWeakSheafify (smallTopology X R) (Type w)]
  [HasWeakSheafify (smallTopology X S) (Type w)]

/-- Small pro-étale direct images compose canonically by iterated base change. -/
def smallMorphism_comp_pushforwardIso :
    (MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f)).pushforward ≅
      (smallMorphism (f ≫ g)).pushforward :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (smallPullbackCompIso f g) (Type w) _
    (smallTopology X T) (smallTopology X S) (smallTopology X R)
    (smallPullback_isContinuous g) (smallPullback_isContinuous f)
    (smallPullback_isContinuous (f ≫ g))

/-- Small pro-étale inverse images compose canonically as the adjunction mate
of the direct-image composition comparison. -/
def smallMorphism_inverseImage_compIso :
    (MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f)).inverseImage ≅
      (smallMorphism (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointUniq
    ((MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f)).adjunction.ofNatIsoRight
      (smallMorphism_comp_pushforwardIso f g))
    (smallMorphism (f ≫ g)).adjunction

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite
