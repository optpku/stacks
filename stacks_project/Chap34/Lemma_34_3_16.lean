/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u

/- Lemma 34.3.16: a morphism of schemes induces the big Zariski morphism of topoi from
sheaves over its source to sheaves over its target. -/
@[stacks 0210] #check
  (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) →
      MorphismOfTopoiIn S.bigZariskiTopology T.bigZariskiTopology)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.map :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over T ⥤ Over S)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.pullback :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) → Over S ⥤ Over T)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.map_isCocontinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Zariski.Big.map f).IsCocontinuous
        T.bigZariskiTopology S.bigZariskiTopology)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.mapPullbackAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      AlgebraicGeometry.Scheme.Zariski.Big.map f ⊣
        AlgebraicGeometry.Scheme.Zariski.Big.pullback f)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.pullback_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Zariski.Big.pullback f).IsContinuous
        S.bigZariskiTopology T.bigZariskiTopology)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi_pushforwardIsoPullbackPresentation :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi f).pushforward ≅
        AlgebraicGeometry.Scheme.Zariski.Big.continuousDirectImage f)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.inverseImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T),
      (((AlgebraicGeometry.Scheme.Zariski.Big.inverseImage f).obj 𝒢).obj.obj (op U)) =
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Zariski.Big.map f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi_inverseImage_objObjIso :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T),
      (((AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj
          (op U) ≅
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Zariski.Big.map f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.continuousDirectImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S),
      (((AlgebraicGeometry.Scheme.Zariski.Big.continuousDirectImage f).obj ℱ).obj.obj
          (op U)) =
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Zariski.Big.pullback f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi_pushforward_objObjIso :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S),
      (((AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi f).pushforward.obj ℱ).obj.obj
          (op U)) ≅
        ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Zariski.Big.pullback f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.lowerShriekAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))],
      AlgebraicGeometry.Scheme.Zariski.Big.lowerShriek f ⊣
        AlgebraicGeometry.Scheme.Zariski.Big.inverseImage f)

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.lowerShriek_preservesPullbacks :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))],
      PreservesLimitsOfShape WalkingCospan
        (AlgebraicGeometry.Scheme.Zariski.Big.lowerShriek f))

#check
  (AlgebraicGeometry.Scheme.Zariski.Big.lowerShriek_preservesEqualizers :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))],
      PreservesLimitsOfShape WalkingParallelPair
        (AlgebraicGeometry.Scheme.Zariski.Big.lowerShriek f))
