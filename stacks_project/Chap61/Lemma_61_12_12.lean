module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig

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
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor_isCocontinuous f :
    Functor.IsCocontinuous
      (SmallToBig.relocalizationFunctor f)
      (smallTopology X T) (bigTopology X S))

/- Lemma 61.12.12 (2): the relocalization induces a morphism from the small
pro-étale topos of `T` to the big pro-étale slice topos over `S`. -/
@[stacks 098P] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.morphismOfTopoi f :
    MorphismOfTopoiIn.{max u v, max u v, u, u, max u v}
      (bigTopology X S) (smallTopology X T))

/- Lemma 61.12.12 (3): inverse image is computed by evaluating on the same
object viewed over `S`. -/
@[stacks 098P] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (bigTopology X S) (Type (max u v)))
      (U : smallSite X T),
      ((SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op ((SmallToBig.relocalizationFunctor f).obj U)))

/- Lemma 61.12.12 (4): lower shriek is left adjoint to inverse image. -/
@[stacks 098P] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.lowerShriekAdjunction.{u, v, max u v} f :
    (SmallToBig.lowerShriek.{u, v, max u v} f :
        Sheaf (smallTopology X T) (Type (max u v)) ⥤
          Sheaf (bigTopology X S) (Type (max u v))) ⊣
      (SmallToBig.inverseImage.{u, v, max u v} f :
        Sheaf (bigTopology X S) (Type (max u v)) ⥤
          Sheaf (smallTopology X T) (Type (max u v))))

/- Lemma 61.12.12 (5): lower shriek preserves fibre products. -/
@[stacks 098P] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan
      (SmallToBig.lowerShriek.{u, v, max u v} f))

/- Lemma 61.12.12 (6): lower shriek preserves equalizers. -/
@[stacks 098P] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair
      (SmallToBig.lowerShriek.{u, v, max u v} f))

end AlgebraicGeometry.ChosenBigProetaleSite
