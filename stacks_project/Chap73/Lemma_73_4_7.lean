module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
open Etale.SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Lemma 73.4.7 (1): the inclusion functor from the spaces-étale site of `Y` to
the big étale slice over `X` is cocontinuous. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationFunctor_isCocontinuous f :
    Functor.IsCocontinuous (relocalizationFunctor f)
      (spacesEtaleTopology Y) (overEtaleTopology X))

/- Lemma 73.4.7 (2): the relocalization induces a morphism from the small étale
topos of `Y` to the big étale slice topos over `X`. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.morphismOfTopoi f :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (overEtaleTopology X) (spacesEtaleTopology Y))

/- Lemma 73.4.7 (3): inverse image is computed by evaluating on the same
étale algebraic space viewed over `X`. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : spacesEtaleSite Y),
      ((inverseImage f).obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op ((relocalizationFunctor f).obj U)))

/- Lemma 73.4.7 (4): lower shriek is left adjoint to inverse image. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.lowerShriekAdjunction.{u, u + 1} f :
    lowerShriek.{u, u + 1} f ⊣ inverseImage.{u, u + 1} f)

/- Lemma 73.4.7 (5): lower shriek preserves fibre products. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.lowerShriek_preservesPullbacks.{u, u + 1} f :
    PreservesLimitsOfShape WalkingCospan (lowerShriek.{u, u + 1} f))

/- Lemma 73.4.7 (6): lower shriek preserves equalizers. -/
@[stacks 0DF2] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.lowerShriek_preservesEqualizers.{u, u + 1} f :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek.{u, u + 1} f))

end AlgebraicGeometry.AlgebraicSpace
