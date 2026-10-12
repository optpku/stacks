/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_12_12_SmallToBig

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

/- Lemma 61.12.12 (1): the relocalization functor is cocontinuous. -/
@[stacks 098P] #check
  (SmallToBig.relocalizationFunctor_isCocontinuous f :
    Functor.IsCocontinuous
      (SmallToBig.relocalizationFunctor f)
      (smallTopology X T) (bigTopology X S))

/- Lemma 61.12.12 (2): the relocalization induces a morphism from the small
pro-étale topos of `T` to the big pro-étale slice topos over `S`. -/
@[stacks 098P] #check
  (SmallToBig.morphismOfTopoi f :
    MorphismOfTopoiIn.{max u v, max u v, v, v, max u v}
      (bigTopology X S) (smallTopology X T))

/- Lemma 61.12.12 (3): inverse image is computed by evaluating on the same
object viewed over `S`. -/
@[stacks 098P] #check
  (SmallToBig.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (bigTopology X S) (Type (max u v)))
      (U : smallSite X T),
      ((SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op ((SmallToBig.relocalizationFunctor f).obj U)))

/- Lemma 61.12.12 (4): lower shriek is left adjoint to inverse image. -/
@[stacks 098P] #check
  (SmallToBig.lowerShriekAdjunction.{u, v, max u v} f :
    (SmallToBig.lowerShriek.{u, v, max u v} f :
        Sheaf (smallTopology X T) (Type (max u v)) ⥤
          Sheaf (bigTopology X S) (Type (max u v))) ⊣
      (SmallToBig.inverseImage.{u, v, max u v} f :
        Sheaf (bigTopology X S) (Type (max u v)) ⥤
          Sheaf (smallTopology X T) (Type (max u v))))

/- Lemma 61.12.12 (5): lower shriek preserves fibre products. -/
@[stacks 098P] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesPullbacks
      (SmallToBig.relocalizationFunctor f) :
    PreservesLimitsOfShape WalkingCospan
      (SmallToBig.lowerShriek.{u, v, max u v} f))

/- Lemma 61.12.12 (6): lower shriek preserves equalizers. -/
@[stacks 098P] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesEqualizers
      (SmallToBig.relocalizationFunctor f) :
    PreservesLimitsOfShape WalkingParallelPair
      (SmallToBig.lowerShriek.{u, v, max u v} f))

end AlgebraicGeometry.ChosenBigProetaleSite
