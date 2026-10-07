module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Compatibility name for the small-to-big étale relocalization functor. -/
abbrev smallEtaleToBigEtaleFunctor : T.Etale ⥤ Over S :=
  Etale.SmallToBig.relocalizationFunctor f

/-- Compatibility name for the morphism of topoi induced by étale relocalization. -/
noncomputable abbrev smallEtaleToBigEtaleMorphismOfTopoi
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    MorphismOfTopoiIn (S.overGrothendieckTopology @Etale) T.smallEtaleTopology :=
  Etale.SmallToBig.morphismOfTopoi f

/- Lemma 34.4.13 (1): the relocalization functor is cocontinuous. -/
@[stacks 021F] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor_isCocontinuous f :
    Functor.IsCocontinuous
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f)
      T.smallEtaleTopology (S.overGrothendieckTopology @Etale))

/- Lemma 34.4.13 (2): the relocalization induces a morphism from the small
étale topos of `T` to the big étale slice topos over `S`. -/
@[stacks 021F] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi f :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (S.overGrothendieckTopology @Etale) T.smallEtaleTopology)

/- Lemma 34.4.13 (3): inverse image is computed by evaluating on the same
étale scheme viewed over `S`. -/
@[stacks 021F] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
      (U : T.Etale),
      ((AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op
          ((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f).obj U)))

/- Lemma 34.4.13 (4): lower shriek is left adjoint to inverse image. -/
@[stacks 021F] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.lowerShriekAdjunction.{u, u + 1} f :
    (AlgebraicGeometry.Scheme.Etale.SmallToBig.lowerShriek.{u, u + 1} f :
        Sheaf T.smallEtaleTopology (Type (u + 1)) ⥤
          Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1))) ⊣
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage.{u, u + 1} f :
        Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
          Sheaf T.smallEtaleTopology (Type (u + 1))))

/- Lemma 34.4.13 (5): lower shriek preserves fibre products. -/
@[stacks 021F] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesPullbacks
      (u := AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f)
      (J := T.smallEtaleTopology) (K := S.overGrothendieckTopology @Etale) :
    PreservesLimitsOfShape WalkingCospan
      ((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f).sheafPullback
        (Type (u + 1)) T.smallEtaleTopology (S.overGrothendieckTopology @Etale)))

/- Lemma 34.4.13 (6): lower shriek preserves equalizers. -/
@[stacks 021F] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesEqualizers
      (u := AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f)
      (J := T.smallEtaleTopology) (K := S.overGrothendieckTopology @Etale) :
    PreservesLimitsOfShape WalkingParallelPair
      ((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f).sheafPullback
        (Type (u + 1)) T.smallEtaleTopology (S.overGrothendieckTopology @Etale)))

end AlgebraicGeometry.Scheme
