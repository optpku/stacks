module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u

/- Lemma 34.4.16: a scheme morphism induces the big étale morphism of topoi from
sheaves over its source to sheaves over its target. -/
@[stacks 021H] #check
  (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) →
      MorphismOfTopoiIn
        (S.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (T.overGrothendieckTopology @AlgebraicGeometry.Etale))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.map :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over T ⥤ Over S)

#check
  (AlgebraicGeometry.Scheme.Etale.Big.pullback :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over S ⥤ Over T)

#check
  (AlgebraicGeometry.Scheme.Etale.Big.map_isCocontinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Etale.Big.map f).IsCocontinuous
        (T.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (S.overGrothendieckTopology @AlgebraicGeometry.Etale))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.map_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Etale.Big.map f).IsContinuous
        (T.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (S.overGrothendieckTopology @AlgebraicGeometry.Etale))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.mapPullbackAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      AlgebraicGeometry.Scheme.Etale.Big.map f ⊣
        AlgebraicGeometry.Scheme.Etale.Big.pullback f)

#check
  (AlgebraicGeometry.Scheme.Etale.Big.pullback_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Etale.Big.pullback f).IsContinuous
        (S.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (T.overGrothendieckTopology @AlgebraicGeometry.Etale))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi_pushforwardIsoPullbackPresentation :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f).pushforward ≅
        AlgebraicGeometry.Scheme.Etale.Big.continuousDirectImage f)

#check
  (AlgebraicGeometry.Scheme.Etale.Big.inverseImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (𝒢 : Sheaf (S.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (Type (u + 1))) (U : Over T),
      (((AlgebraicGeometry.Scheme.Etale.Big.inverseImage f).obj 𝒢).obj.obj (op U)) =
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Etale.Big.map f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi_inverseImage_objObjIso :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (𝒢 : Sheaf (S.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (Type (u + 1))) (U : Over T),
      (((AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj
          (op U) ≅
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Etale.Big.map f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.continuousDirectImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (ℱ : Sheaf (T.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (Type (u + 1))) (U : Over S),
      (((AlgebraicGeometry.Scheme.Etale.Big.continuousDirectImage f).obj ℱ).obj.obj
          (op U)) =
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Etale.Big.pullback f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi_pushforward_objObjIso :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (ℱ : Sheaf (T.overGrothendieckTopology @AlgebraicGeometry.Etale)
        (Type (u + 1))) (U : Over S),
      (((AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f).pushforward.obj ℱ).obj.obj
          (op U)) ≅
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Etale.Big.pullback f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.lowerShriekAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      AlgebraicGeometry.Scheme.Etale.Big.lowerShriek f ⊣
        AlgebraicGeometry.Scheme.Etale.Big.inverseImage f)

#check
  (AlgebraicGeometry.Scheme.Etale.Big.lowerShriek_preservesPullbacks :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      PreservesLimitsOfShape WalkingCospan
        (AlgebraicGeometry.Scheme.Etale.Big.lowerShriek f))

#check
  (AlgebraicGeometry.Scheme.Etale.Big.lowerShriek_preservesEqualizers :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      PreservesLimitsOfShape WalkingParallelPair
        (AlgebraicGeometry.Scheme.Etale.Big.lowerShriek f))
