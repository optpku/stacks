/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_12_15_Big

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier} (f : T ⟶ S)

/- Lemma 61.12.15 (1): postcomposition on chosen big pro-étale slices is
cocontinuous. -/
@[stacks 098S] #check
  (Big.map_isCocontinuous f :
    Functor.IsCocontinuous (Big.map f) (bigTopology X T) (bigTopology X S))

/- Lemma 61.12.15 (2): postcomposition has a continuous right adjoint given by
pullback along `f`. -/
@[stacks 098S] #check
  (Big.mapPullbackAdjunction f : Big.map f ⊣ Big.pullback f)

@[stacks 098S] #check
  (Big.pullback_isContinuous f :
    Functor.IsContinuous (Big.pullback f) (bigTopology X S) (bigTopology X T))

/- Lemma 61.12.15 (3): postcomposition and pullback induce the same morphism of
topoi from the big pro-étale topos of `T` to that of `S`. -/
@[stacks 098S] #check
  (Big.morphismOfTopoi f :
    MorphismOfTopoiIn.{max u v, max u v, v, v, max u v}
      (bigTopology X S) (bigTopology X T))

/- Lemma 61.12.15 (4): inverse image is computed by evaluating on the same
object viewed over `S`. -/
@[stacks 098S] #check
  (Big.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (bigTopology X S) (Type (max u v))) (U : bigSite X T),
      ((Big.inverseImage f).obj 𝒢).obj.obj (op U) =
        𝒢.obj.obj (op ((Big.map f).obj U)))

/- Lemma 61.12.15 (5): direct image is computed by evaluating on the fibre
product over `T`. -/
@[stacks 098S] #check
  (Big.continuousDirectImage_obj_obj f :
    ∀ (ℱ : Sheaf (bigTopology X T) (Type (max u v))) (U : bigSite X S),
      ((Big.continuousDirectImage f).obj ℱ).obj.obj (op U) =
        ℱ.obj.obj (op ((Big.pullback f).obj U)))

/- Lemma 61.12.15 (6): inverse image has a left adjoint given by lower
shriek. -/
@[stacks 098S] #check
  (Big.lowerShriekAdjunction.{u, v, max u v} f :
    (Big.lowerShriek.{u, v, max u v} f :
        Sheaf (bigTopology X T) (Type (max u v)) ⥤
          Sheaf (bigTopology X S) (Type (max u v))) ⊣
      (Big.inverseImage.{u, v, max u v} f :
        Sheaf (bigTopology X S) (Type (max u v)) ⥤
          Sheaf (bigTopology X T) (Type (max u v))))

/- Lemma 61.12.15 (7): lower shriek preserves fibre products. -/
@[stacks 098S] #check
  (Big.lowerShriek_preservesPullbacks.{u, v, max u v} f :
    PreservesLimitsOfShape WalkingCospan (Big.lowerShriek.{u, v, max u v} f))

/- Lemma 61.12.15 (8): lower shriek preserves equalizers. -/
@[stacks 098S] #check
  (Big.lowerShriek_preservesEqualizers.{u, v, max u v} f :
    PreservesLimitsOfShape WalkingParallelPair
      (Big.lowerShriek.{u, v, max u v} f))

end AlgebraicGeometry.ChosenBigProetaleSite
