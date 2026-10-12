/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
import ReasLib.CategoryTheory.Sites.Over.ToposWithPullbacks
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u v

variable (X : AlgebraicGeometry.ChosenBigHSite.{u, v})
  {S T : X.carrier} (f : T ⟶ S)

/- Lemma 38.34.18 (1): postcomposition from the big h slice over `T` to the
big h slice over `S` is cocontinuous. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.mapFunctor_isCocontinuous
      X.toGrothendieck f :
    Functor.IsCocontinuous (CategoryTheory.Over.Site.mapFunctor f)
      (X.toGrothendieck.over T) (X.toGrothendieck.over S))

/- Lemma 38.34.18 (2): postcomposition is left adjoint to pullback. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.mapPullbackAdjunction
      X.hasPullbacks f :
    CategoryTheory.Over.Site.mapFunctor f ⊣
      CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor X.hasPullbacks f)

/- Lemma 38.34.18 (3): pullback between the big h slices is continuous. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor_isContinuous
      X.toGrothendieck X.hasPullbacks f :
    Functor.IsContinuous
      (CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor X.hasPullbacks f)
      (X.toGrothendieck.over S) (X.toGrothendieck.over T))

/- Lemma 38.34.18 (4): the adjoint slice functors induce the canonical
morphism of topoi from the big h topos over `T` to that over `S`. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.morphismOfTopoi.{u, v, max u v}
      X.toGrothendieck f :
    MorphismOfTopoiIn
      (X.toGrothendieck.over S) (X.toGrothendieck.over T))

/- Lemma 38.34.18 (5): the inverse image of the induced morphism of topoi is
the sheaf functor obtained from postcomposition. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.Morphism.inverseImage.{u, v, max u v}
      X.toGrothendieck f :
    (CategoryTheory.Over.Site.morphismOfTopoi.{u, v, max u v}
      X.toGrothendieck f)⁻¹ =
        CategoryTheory.Over.Site.inverseImage X.toGrothendieck f)

/- Lemma 38.34.18 (6): the cocontinuous and continuous-pullback
presentations of direct image induce the same morphism of topoi. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.Morphism.pushforwardPresentation.{u, v, max u v}
      X.toGrothendieck X.hasPullbacks f :
    (CategoryTheory.Over.Site.morphismOfTopoi.{u, v, max u v}
      X.toGrothendieck f).pushforward ≅
        (
         -- Local instance justification (proof-local temporary data): `sheafPushforwardContinuous` accepts continuity only as a typeclass argument.
         letI := CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor_isContinuous
          X.toGrothendieck X.hasPullbacks f
         (CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor
          X.hasPullbacks f).sheafPushforwardContinuous (Type (max u v))
            (X.toGrothendieck.over S) (X.toGrothendieck.over T)))

section

variable
  (G : Sheaf (X.toGrothendieck.over S) (Type (max u v))) (U : Over T)

/- Lemma 38.34.18 (7): inverse image is computed by evaluating on the
postcomposed slice object `U/S`. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.InverseImage.obj_eq.{u, v, max u v}
      X.toGrothendieck f G U :
    ((CategoryTheory.Over.Site.inverseImage X.toGrothendieck f).obj G).obj.obj (op U) =
      G.obj.obj (op ((CategoryTheory.Over.Site.mapFunctor f).obj U)))

end

section

variable
  (F : Sheaf (X.toGrothendieck.over T) (Type (max u v))) (U : Over S)

/- Lemma 38.34.18 (8): direct image is computed by evaluating on the
pullback slice object `U ×_S T/T`. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.DirectImage.obj_eq.{u, v, max u v}
      X.toGrothendieck X.hasPullbacks f F U :
    ((CategoryTheory.Over.Site.directImage X.toGrothendieck f).obj F).obj.obj (op U) =
      F.obj.obj (op ((CategoryTheory.Over.Site.WithPullbacks.pullbackFunctor
        X.hasPullbacks f).obj U)))

end

/- Lemma 38.34.18 (9): lower shriek is left adjoint to the inverse image of
the induced morphism of topoi. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.LowerShriek.adjunction_viaMorphism.{u, v, max u v}
      X.toGrothendieck f :
    CategoryTheory.Over.Site.lowerShriek X.toGrothendieck f ⊣
      (CategoryTheory.Over.Site.morphismOfTopoi.{u, v, max u v}
        X.toGrothendieck f)⁻¹)

/- Lemma 38.34.18 (10): lower shriek preserves fibre products. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.LowerShriek.preservesPullbacks.{u, v, max u v}
      X.toGrothendieck X.hasPullbacks f :
    PreservesLimitsOfShape WalkingCospan
      (CategoryTheory.Over.Site.lowerShriek X.toGrothendieck f))

/- Lemma 38.34.18 (11): lower shriek preserves equalizers. -/
@[stacks 0EU6] #check
  (CategoryTheory.Over.Site.WithPullbacks.LowerShriek.preservesEqualizers.{u, v, max u v}
      X.toGrothendieck X.hasPullbacks f :
    PreservesLimitsOfShape WalkingParallelPair
      (CategoryTheory.Over.Site.lowerShriek X.toGrothendieck f))
