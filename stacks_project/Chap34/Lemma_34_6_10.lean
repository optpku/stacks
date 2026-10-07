module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Big
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u

/- Lemma 34.6.10 (1): big-syntomic postcomposition is cocontinuous. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.map_isCocontinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Syntomic.Big.map f).IsCocontinuous
        (AlgebraicGeometry.Scheme.syntomicOverTopology T)
        (AlgebraicGeometry.Scheme.syntomicOverTopology S))

/- Lemma 34.6.10 (2): big-syntomic postcomposition is continuous. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.map_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Syntomic.Big.map f).IsContinuous
        (AlgebraicGeometry.Scheme.syntomicOverTopology T)
        (AlgebraicGeometry.Scheme.syntomicOverTopology S))

/- Lemma 34.6.10 (3): big-syntomic postcomposition is left adjoint to pullback. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.mapPullbackAdjunction :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      AlgebraicGeometry.Scheme.Syntomic.Big.map f ⊣
        AlgebraicGeometry.Scheme.Syntomic.Big.pullback f)

/- Lemma 34.6.10 (4): big-syntomic pullback is continuous. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.pullback_isContinuous :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).IsContinuous
        (AlgebraicGeometry.Scheme.syntomicOverTopology S)
        (AlgebraicGeometry.Scheme.syntomicOverTopology T))

/- Lemma 34.6.10 (5): the cocontinuous and continuous-right-adjoint presentations have
the same direct image. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.morphismOfTopoi_pushforwardIsoPullbackPresentation :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S),
      (AlgebraicGeometry.Scheme.Syntomic.Big.morphismOfTopoi f).pushforward ≅
        AlgebraicGeometry.Scheme.Syntomic.Big.continuousDirectImage f)

/- Lemma 34.6.10 (6): inverse image is evaluated by postcomposition on slice objects. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.inverseImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (𝒢 : Sheaf (AlgebraicGeometry.Scheme.syntomicOverTopology S) (Type (u + 1)))
      (U : Over T),
      (((AlgebraicGeometry.Scheme.Syntomic.Big.inverseImage f).obj 𝒢).obj.obj (op U)) =
        𝒢.obj.obj (op ((AlgebraicGeometry.Scheme.Syntomic.Big.map f).obj U)))

/- Lemma 34.6.10 (7): continuous direct image is evaluated on the pullback slice object. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.continuousDirectImage_obj_obj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      (ℱ : Sheaf (AlgebraicGeometry.Scheme.syntomicOverTopology T) (Type (u + 1)))
      (U : Over S),
      (((AlgebraicGeometry.Scheme.Syntomic.Big.continuousDirectImage f).obj ℱ).obj.obj
          (op U)) =
        ℱ.obj.obj
          (op ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).obj U)))

/- Lemma 34.6.10 (8): lower shriek is left adjoint to the bundled inverse image. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriekAdjunction_via_morphism :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify (AlgebraicGeometry.Scheme.syntomicOverTopology S)
        (Type (u + 1))],
      AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriek f ⊣
        (AlgebraicGeometry.Scheme.Syntomic.Big.morphismOfTopoi f)⁻¹)

/- Lemma 34.6.10 (9): lower shriek preserves pullbacks. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriek_preservesPullbacks :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify (AlgebraicGeometry.Scheme.syntomicOverTopology S)
        (Type (u + 1))],
      PreservesLimitsOfShape WalkingCospan
        (AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriek f))

/- Lemma 34.6.10 (10): lower shriek preserves equalizers. -/
@[stacks 04HD] #check
  (AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriek_preservesEqualizers :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [HasWeakSheafify (AlgebraicGeometry.Scheme.syntomicOverTopology S)
        (Type (u + 1))],
      PreservesLimitsOfShape WalkingParallelPair
        (AlgebraicGeometry.Scheme.Syntomic.Big.lowerShriek f))
