/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Comparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Compatibility checks for the promoted h-to-étale comparison API. -/
#check (AlgebraicGeometry.Scheme.HComparison.identity_isMorphismOfSites :
  ∀ (X : Scheme.{u}),
    IsMorphismOfSites (Scheme.etaleTopology.over X)
      (AlgebraicGeometry.Scheme.H.Big.site X) (𝟭 (Over X)))
#check (AlgebraicGeometry.Scheme.HComparison.identitySheafPullback_preservesFiniteLimits :
  ∀ (X : Scheme.{u}),
    Limits.PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (𝟭 (Over X)) (Type (u + 1)) _
        (Scheme.etaleTopology.over X)
        (AlgebraicGeometry.Scheme.H.Big.site X)
        (AlgebraicGeometry.Scheme.HComparison.identity_isMorphismOfSites X).toIsContinuous
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          _ _ _ _ (𝟭 (Over X)) (Type (u + 1)) _
          (Scheme.etaleTopology.over X) (AlgebraicGeometry.Scheme.H.Big.site X)
          (AlgebraicGeometry.Scheme.HComparison.identity_isMorphismOfSites X).toIsContinuous
          (fun _ => inferInstance)
          (AlgebraicGeometry.Scheme.H.Big.hasWeakSheafify X)).isRightAdjoint))
#check (AlgebraicGeometry.Scheme.HComparison.epsilon :
  ∀ (X : Scheme.{u}),
    MorphismOfTopoiIn (Scheme.etaleTopology.over X)
      (AlgebraicGeometry.Scheme.H.Big.site X))
#check (AlgebraicGeometry.Scheme.HComparison.bigHEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (AlgebraicGeometry.Scheme.H.Big.morphismOfTopoi f.left).pushforward
      (AlgebraicGeometry.Scheme.HComparison.epsilon X.left).pushforward
      (AlgebraicGeometry.Scheme.HComparison.epsilon Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward))
#check (AlgebraicGeometry.Scheme.HComparison.hSmallEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (AlgebraicGeometry.Scheme.H.Big.morphismOfTopoi f.left).pushforward
      ((AlgebraicGeometry.Scheme.HComparison.epsilon X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((AlgebraicGeometry.Scheme.HComparison.epsilon Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward))

end

end
