/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Presheaf.Sheaf
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.Sites.Presheaf.Pushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open AlgebraicGeometry.FiberedInGroupoids
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

#check (CategoryTheory.CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor f) (τ.overTopology S) :
  (toFunctor f).IsContinuous (X.associatedTopology τ) (Y.associatedTopology τ))

#check (CategoryTheory.CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (τ.overTopology S) :
  (toFunctor f).IsCocontinuous (X.associatedTopology τ) (Y.associatedTopology τ))

/- The continuity and cocontinuity witnesses are supplied explicitly: the cartesian
functor cannot be reconstructed by instance inference from its total-functor projection. -/
#check (@CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf
    _ _ _ _ (toFunctor f) (Type w) _ (X.associatedTopology τ) (Y.associatedTopology τ)
    (CartesianBasedFunctor.inheritedTopology.isContinuous
      (toCartesianBasedFunctor f) (τ.overTopology S)) :
  ∀ G : Y.totalᵒᵖ ⥤ Type w, IsSheafFor Y.p τ G →
    IsSheafFor X.p τ ((presheafInverseImage (toFunctor f) (Type w)).obj G))

/- The coefficient universe agrees with the presheaf pushforward of 96.3.1.1.
It supplies the pointwise limits and sheafification without extra existence assumptions. -/
#check (@CategoryTheory.ran_isSheaf_of_isCocontinuous
    _ _ _ _ (toFunctor f) (Type (max (u + 1) w)) _
    (X.associatedTopology τ) (Y.associatedTopology τ)
    (CartesianBasedFunctor.inheritedTopology.isCocontinuous
      (toCartesianBasedFunctor f) (τ.overTopology S)) _ :
  ∀ F : Sheaf (X.associatedTopology τ) (Type (max (u + 1) w)),
    IsSheafFor Y.p τ ((presheafPushforward (toFunctor f)).obj F.obj))

/- Lemma 96.4.4: for every morphism of categories fibred in groupoids and each
of the Zariski, étale, smooth, syntomic, and fppf topologies, the prescribed
presheaf functors preserve sheaves and induce `Sh(X_τ) ⟶ Sh(Y_τ)`. -/
@[stacks 06TS] #check
  (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn.{_, _, _, _, _, _, max (u + 1) w}
    (toCartesianBasedFunctor f) (τ.overTopology S) :
    MorphismOfTopoiIn.{_, _, _, _, max (u + 1) w}
      (Y.associatedTopology τ) (X.associatedTopology τ))

#check (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn.pushforward_eq.{_, _, _, _, _, _, max (u + 1) w}
    (toCartesianBasedFunctor f) (τ.overTopology S) :
  (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn.{_, _, _, _, _, _, max (u + 1) w}
    (toCartesianBasedFunctor f) (τ.overTopology S)).pushforward =
    (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
      (Type (max (u + 1) w)) (X.associatedTopology τ) (Y.associatedTopology τ))

#check (@CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
    _ _ _ _ (toFunctor f) (Type (max (u + 1) w)) _
    (X.associatedTopology τ) (Y.associatedTopology τ)
    (CartesianBasedFunctor.inheritedTopology.isCocontinuous
      (toCartesianBasedFunctor f) (τ.overTopology S)) _ :
  (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
      (Type (max (u + 1) w)) (X.associatedTopology τ) (Y.associatedTopology τ) ⋙
      sheafToPresheaf (Y.associatedTopology τ) (Type (max (u + 1) w)) ≅
    sheafToPresheaf (X.associatedTopology τ) (Type (max (u + 1) w)) ⋙
      presheafPushforward (toFunctor f))

#check (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso.{_, _, _, _, _, _, max (u + 1) w}
    (toCartesianBasedFunctor f) (τ.overTopology S) :
  (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn.{_, _, _, _, _, _, max (u + 1) w}
    (toCartesianBasedFunctor f) (τ.overTopology S)).inverseImage ≅
    (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
      (Type (max (u + 1) w)) (X.associatedTopology τ) (Y.associatedTopology τ))

#check (@CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso
    _ _ _ _ (toFunctor f) (Type (max (u + 1) w)) _
    (X.associatedTopology τ) (Y.associatedTopology τ)
    (CartesianBasedFunctor.inheritedTopology.isContinuous
      (toCartesianBasedFunctor f) (τ.overTopology S)) :
  (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
      (Type (max (u + 1) w)) (X.associatedTopology τ) (Y.associatedTopology τ) ⋙
      sheafToPresheaf (X.associatedTopology τ) (Type (max (u + 1) w)) ≅
    sheafToPresheaf (Y.associatedTopology τ) (Type (max (u + 1) w)) ⋙
      presheafInverseImage (toFunctor f) (Type (max (u + 1) w)))

end AlgebraicGeometry.GroupoidsOver
