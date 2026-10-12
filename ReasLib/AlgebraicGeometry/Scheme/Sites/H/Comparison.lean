/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Big
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

/-!
# Comparison between big h and étale sites

This leaf packages the comparison morphisms and their functoriality for
schemes over a fixed base.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- The identity site functor gives the h-to-étale comparison on a slice. -/
def identity_isMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites (Scheme.etaleTopology.over X)
      (H.Big.site X) (𝟭 (CategoryTheory.Over X)) := sorry

/-- Pullback along the identity h-to-étale comparison is left exact. -/
def identitySheafPullback_preservesFiniteLimits (X : Scheme.{u}) :
    Limits.PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (𝟭 (CategoryTheory.Over X)) (Type (u + 1)) _
        (Scheme.etaleTopology.over X) (H.Big.site X)
        (identity_isMorphismOfSites X).toIsContinuous
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          _ _ _ _ (𝟭 (CategoryTheory.Over X)) (Type (u + 1)) _
          (Scheme.etaleTopology.over X) (H.Big.site X)
          (identity_isMorphismOfSites X).toIsContinuous
          (fun _ => inferInstance) (H.Big.hasWeakSheafify X)).isRightAdjoint) := sorry

/-- The comparison morphism from the big h topos to the big étale topos. -/
noncomputable def epsilon (X : Scheme.{u}) :
    MorphismOfTopoiIn (Scheme.etaleTopology.over X) (H.Big.site X) :=
  (@IsMorphismOfSites.toMorphismOfTopoiIn _ _ _ _
    (Scheme.etaleTopology.over X) (H.Big.site X) (𝟭 (CategoryTheory.Over X))
    (identity_isMorphismOfSites X) (H.Big.hasWeakSheafify X)
    (fun _ => inferInstance)
    (identitySheafPullback_preservesFiniteLimits X) :
    LeftExactAdjunction
      (Sheaf (H.Big.site X) (Type (u + 1)))
      (Sheaf (Scheme.etaleTopology.over X) (Type (u + 1))))

/-- The h-to-étale comparison commutes with the big direct-image functors. -/
theorem bigHEtaleCommSq {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (H.Big.morphismOfTopoi f.left).pushforward
      (epsilon X.left).pushforward
      (epsilon Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward) := sorry

/-- The h-to-étale comparison commutes after composing with small-to-big
étale direct images. -/
theorem hSmallEtaleCommSq {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (H.Big.morphismOfTopoi f.left).pushforward
      ((epsilon X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((epsilon Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
