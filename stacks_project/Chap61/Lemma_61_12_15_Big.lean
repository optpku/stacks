/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Definition_61_12_8_Presentation
public import stacks_project.Chap61.Lemma_61_12_10_Limits
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big pro-étale morphisms of topoi on a chosen site

This leaf specializes the slice-site morphism of topoi attached to a carrier
morphism `f : T ⟶ S` in a chosen big pro-étale presentation.  The underlying
functors are `Over.map` and `Over.pullback`; the declarations here name the
chosen-site topologies and the induced sheaf and topos functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace Big

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier}

/-- The carrier of a chosen big pro-étale presentation has fibre products. -/
instance carrier_hasPullbacks (X : ChosenBigProetaleSite.{u, v}) :
    HasPullbacks X.carrier :=
  X.hasPullbacks

/-- The chosen big pro-étale slice over an object has fibre products. -/
instance bigSite_hasPullbacks (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    HasPullbacks (bigSite X S) :=
  ChosenBigSite.sliceHasPullbacks X S

/-- The chosen big pro-étale slice over an object has equalizers. -/
instance bigSite_hasEqualizers (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    HasEqualizers (bigSite X S) :=
  bigSiteHasEqualizers X S

/-- Pullbacks along a morphism in a chosen big pro-étale carrier exist. -/
instance hasPullbacksAlong_map (f : T ⟶ S) : HasPullbacksAlong f :=
  inferInstance

/-- Postcomposition on chosen big pro-étale slices. On objects it sends `V / T`
to `V / S`. -/
abbrev map (f : T ⟶ S) : bigSite X T ⥤ bigSite X S :=
  Over.map f

/-- Pullback on chosen big pro-étale slices. On objects it sends `U / S` to
`U ×_S T / T`. -/
abbrev pullback (f : T ⟶ S) : bigSite X S ⥤ bigSite X T :=
  Over.pullback f

/-- The canonical postcomposition-pullback adjunction on chosen big pro-étale
slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) : map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Postcomposition is continuous for the chosen big pro-étale slice
topologies. -/
instance map_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (map f) (bigTopology X T) (bigTopology X S) :=
  inferInstanceAs
    ((Over.map f).IsContinuous ((X.toGrothendieck).over T) ((X.toGrothendieck).over S))

/-- Postcomposition is cocontinuous for the chosen big pro-étale slice
topologies. -/
instance map_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (map f) (bigTopology X T) (bigTopology X S) :=
  inferInstanceAs
    ((Over.map f).IsCocontinuous ((X.toGrothendieck).over T) ((X.toGrothendieck).over S))

/-- Pullback is continuous for the chosen big pro-étale slice topologies. -/
instance pullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (pullback f) (bigTopology X S) (bigTopology X T) :=
  inferInstanceAs
    ((Over.pullback f).IsContinuous ((X.toGrothendieck).over S)
      ((X.toGrothendieck).over T))

/-- Chosen big pro-étale postcomposition preserves fibre products. -/
instance Map.preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (map f) := sorry

/-- Chosen big pro-étale postcomposition preserves equalizers. -/
instance Map.preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (map f) := sorry

/-- The opposite postcomposition functor has the left Kan extensions used by
lower shriek. -/
instance map_op_hasLeftKanExtension (f : T ⟶ S) (P : (bigSite X T)ᵒᵖ ⥤ Type w) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The opposite postcomposition functor has the pointwise left Kan extensions
used by finite-connected-limit preservation of lower shriek. -/
instance map_op_hasPointwiseLeftKanExtension
    (f : T ⟶ S) (P : (bigSite X T)ᵒᵖ ⥤ Type w) :
    (map f).op.HasPointwiseLeftKanExtension P := sorry

/-- The opposite postcomposition functor has the pointwise right Kan extensions
used by the cocontinuous direct image. -/
instance map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (bigSite X T)ᵒᵖ ⥤ Type w) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on chosen big pro-étale sheaves. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (bigTopology X T) (Type w) :=
  (map f).sheafPushforwardContinuous (Type w) (bigTopology X T) (bigTopology X S)

/-- The inverse image is computed by evaluating on the postcomposed slice
object. -/
theorem inverseImage_obj_obj (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : bigSite X T) :
    ((inverseImage f).obj 𝒢).obj.obj (op U) =
      𝒢.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : bigSite X T) :
    ((inverseImage f).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type w) 𝒢 U

/-- The direct-image functor presented by cocontinuous chosen big pro-étale
postcomposition. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  (map f).sheafPushforwardCocontinuous (Type w) (bigTopology X T) (bigTopology X S)

/-- The direct-image functor presented by the continuous pullback right
adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  (pullback f).sheafPushforwardContinuous (Type w)
    (bigTopology X S) (bigTopology X T)

/-- The continuous direct image is computed by evaluation on the pullback slice
object. -/
theorem continuousDirectImage_obj_obj (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((continuousDirectImage f).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((pullback f).obj U)) := sorry

/-- The continuous direct-image computation as a canonical objectwise
isomorphism. -/
noncomputable def continuousDirectImage_objObjIso (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((continuousDirectImage f).obj ℱ).obj.obj (op U) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (pullback f) (Type w) ℱ U

/-- The cocontinuous direct image is objectwise identified with evaluation on
the pullback slice object. -/
noncomputable def directImage_objObjIso (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((directImage f).obj ℱ).obj.obj (op U) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type w) (mapPullbackAdjunction f) ℱ U

/-- The continuous and cocontinuous direct-image presentations are canonically
isomorphic. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅ continuousDirectImage f :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type w) (mapPullbackAdjunction f)).symm

/-- The inverse image on chosen big pro-étale sheaves preserves finite
limits. -/
instance inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by chosen big pro-étale
postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn.{max u v, max u v, v, v, w}
      (bigTopology X S) (bigTopology X T) where
  inverseImageFunctor := LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type w) (bigTopology X T) (bigTopology X S)

/-- The inverse-image projection of the bundled chosen big pro-étale
morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled chosen big pro-étale
morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The lower-shriek functor on chosen big pro-étale sheaves. -/
abbrev lowerShriek (f : T ⟶ S) [HasWeakSheafify (bigTopology X S) (Type w)] :
    Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  (map f).sheafPullback (Type w) (bigTopology X T) (bigTopology X S)

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type w) (bigTopology X T) (bigTopology X S)

/-- Lower shriek on chosen big pro-étale sheaves preserves fibre products. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek on chosen big pro-étale sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

end Big
end AlgebraicGeometry.ChosenBigProetaleSite
