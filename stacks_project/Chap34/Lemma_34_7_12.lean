module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MorphismOfTopoiIn

universe u

/-!
# Lemma 34.7.12

The big fppf site functors and their objectwise computation API are owned by
`AlgebraicGeometry.Scheme.Fppf.Big`. This chapter item checks the complete
source-facing surface directly.
-/

/- Lemma 34.7.12: a scheme morphism induces the bundled morphism of topoi on
the corresponding big fppf sites. -/
@[stacks 021W] #check
  (AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) →
      MorphismOfTopoiIn (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.Scheme.fppfTopology.over T))

/- Postcomposition and pullback are the functors between the big fppf slices. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.map :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over T ⥤ Over S)

#check
  (AlgebraicGeometry.Scheme.Fppf.Big.pullback :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over S ⥤ Over T)

/- Postcomposition is cocontinuous and continuous, pullback is continuous, and
the two functors form the canonical adjunction. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.map_isCocontinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      Functor.IsCocontinuous (AlgebraicGeometry.Scheme.Fppf.Big.map f)
        (AlgebraicGeometry.Scheme.fppfTopology.over T)
        (AlgebraicGeometry.Scheme.fppfTopology.over S))

#check
  (AlgebraicGeometry.Scheme.Fppf.Big.map_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      Functor.IsContinuous (AlgebraicGeometry.Scheme.Fppf.Big.map f)
        (AlgebraicGeometry.Scheme.fppfTopology.over T)
        (AlgebraicGeometry.Scheme.fppfTopology.over S))

#check
  (AlgebraicGeometry.Scheme.Fppf.Big.pullback_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      Functor.IsContinuous (AlgebraicGeometry.Scheme.Fppf.Big.pullback f)
        (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.Scheme.fppfTopology.over T))

#check
  (AlgebraicGeometry.Scheme.Fppf.Big.mapPullbackAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      AlgebraicGeometry.Scheme.Fppf.Big.map f ⊣
        AlgebraicGeometry.Scheme.Fppf.Big.pullback f)

section

variable {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)

/- The continuous presentations associated to the adjoint slice functors are adjoint. -/
#check
  (CategoryTheory.Adjunction.sheafPushforwardContinuous
      (AlgebraicGeometry.Scheme.Fppf.Big.mapPullbackAdjunction f)
      (AlgebraicGeometry.Scheme.fppfTopology.over T)
      (AlgebraicGeometry.Scheme.fppfTopology.over S) :
    AlgebraicGeometry.Scheme.Fppf.Big.inverseImage f ⊣
      AlgebraicGeometry.Scheme.Fppf.Big.continuousDirectImage f)

/- The cocontinuous and continuous-right-adjoint presentations of direct image agree. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.directImageIsoPullbackPresentation f :
    AlgebraicGeometry.Scheme.Fppf.Big.directImage f ≅
      AlgebraicGeometry.Scheme.Fppf.Big.continuousDirectImage f)

/- Inverse image is computed by postcomposition on the slice object. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type (u + 1)))
      (U : Over T),
      (((AlgebraicGeometry.Scheme.Fppf.Big.inverseImage f).obj 𝒢).obj.obj (op U)) =
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Fppf.Big.map f).obj U)))

/- Direct image is canonically computed by evaluation on the pullback slice object. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.directImage_objObjIso f :
    ∀ (ℱ : Sheaf (AlgebraicGeometry.Scheme.fppfTopology.over T) (Type (u + 1)))
      (U : Over S),
      (((AlgebraicGeometry.Scheme.Fppf.Big.directImage f).obj ℱ).obj.obj (op U)) ≅
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Fppf.Big.pullback f).obj U)))

/- The continuous direct-image presentation has the corresponding objectwise formula. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.continuousDirectImage_obj_obj f :
    ∀ (ℱ : Sheaf (AlgebraicGeometry.Scheme.fppfTopology.over T) (Type (u + 1)))
      (U : Over S),
      (((AlgebraicGeometry.Scheme.Fppf.Big.continuousDirectImage f).obj ℱ).obj.obj (op U)) =
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Fppf.Big.pullback f).obj U)))

/- The concrete lower-shriek functor is left adjoint to inverse image. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.lowerShriekAdjunction f :
    AlgebraicGeometry.Scheme.Fppf.Big.lowerShriek f ⊣
      AlgebraicGeometry.Scheme.Fppf.Big.inverseImage f)

/- Lower shriek preserves pullbacks and equalizers. -/
#check
  (AlgebraicGeometry.Scheme.Fppf.Big.lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.Scheme.Fppf.Big.lowerShriek f))

#check
  (AlgebraicGeometry.Scheme.Fppf.Big.lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.Scheme.Fppf.Big.lowerShriek f))

end
