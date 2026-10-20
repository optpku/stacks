module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig
public import stacks_project.Chap61.Lemma_61_12_10_Limits

/-!
# Small-to-big pro-étale relocalization on a chosen site

The chosen-presentation relocalization API is available from its mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier} (f : T ⟶ S)

#check (SmallToBig.smallSite_hasPullbacks X T : HasPullbacks (smallSite X T))

#check (SmallToBig.smallSite_hasEqualizers X T : HasEqualizers (smallSite X T))

#check (SmallToBig.relocalizationFunctor f : smallSite X T ⥤ bigSite X S)

#check (SmallToBig.relocalizationFunctor_isContinuous f :
  Functor.IsContinuous (SmallToBig.relocalizationFunctor f)
    (smallTopology X T) (bigTopology X S))

#check (SmallToBig.relocalizationFunctor_isCocontinuous f :
  Functor.IsCocontinuous (SmallToBig.relocalizationFunctor f)
    (smallTopology X T) (bigTopology X S))

#check (SmallToBig.Relocalization.preservesPullbacks f :
  PreservesLimitsOfShape WalkingCospan (SmallToBig.relocalizationFunctor f))

#check (SmallToBig.Relocalization.preservesEqualizers f :
  PreservesLimitsOfShape WalkingParallelPair (SmallToBig.relocalizationFunctor f))

variable [UnivLE.{max u v, w}]

#check (SmallToBig.relocalizationFunctor_op_hasLeftKanExtension f :
  ∀ P : (smallSite X T)ᵒᵖ ⥤ Type w,
    (SmallToBig.relocalizationFunctor f).op.HasLeftKanExtension P)

#check (SmallToBig.relocalizationFunctor_op_hasPointwiseLeftKanExtension f :
  ∀ P : (smallSite X T)ᵒᵖ ⥤ Type w,
    (SmallToBig.relocalizationFunctor f).op.HasPointwiseLeftKanExtension P)

#check (SmallToBig.relocalizationFunctor_op_hasPointwiseRightKanExtension f :
  ∀ P : (smallSite X T)ᵒᵖ ⥤ Type w,
    (SmallToBig.relocalizationFunctor f).op.HasPointwiseRightKanExtension P)

#check (SmallToBig.inverseImage f :
  Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (smallTopology X T) (Type w))

#check (SmallToBig.inverseImage_obj_obj f :
  ∀ (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X T),
    ((SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((SmallToBig.relocalizationFunctor f).obj U)))

#check (SmallToBig.inverseImage_objObjIso f :
  ∀ (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X T),
    ((SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((SmallToBig.relocalizationFunctor f).obj U)))

#check (SmallToBig.directImage f :
  Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w))

#check (SmallToBig.inverseImage_preservesFiniteLimits f :
  PreservesFiniteLimits (SmallToBig.inverseImage.{u, v, w} f))

section

variable [HasWeakSheafify (bigTopology X S) (Type w)]

#check (SmallToBig.lowerShriek f :
  Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w))

#check (SmallToBig.lowerShriekAdjunction f :
  SmallToBig.lowerShriek.{u, v, w} f ⊣ SmallToBig.inverseImage.{u, v, w} f)

end

section

variable [HasSheafify (smallTopology X T) (Type w)]

#check (SmallToBig.morphismOfTopoi f :
  MorphismOfTopoiIn.{max u v, max u v, u, u, w}
    (bigTopology X S) (smallTopology X T))

#check (SmallToBig.morphismOfTopoi_inverseImage f :
  (SmallToBig.morphismOfTopoi.{u, v, w} f)⁻¹ = SmallToBig.inverseImage f)

#check (SmallToBig.morphismOfTopoi_pushforward f :
  (SmallToBig.morphismOfTopoi.{u, v, w} f).pushforward = SmallToBig.directImage f)

end

end AlgebraicGeometry.ChosenBigProetaleSite
