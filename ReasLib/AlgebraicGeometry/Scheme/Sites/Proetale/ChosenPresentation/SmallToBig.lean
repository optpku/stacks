/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Small-to-big pro-étale relocalization on a chosen site

Relocalization sends a weakly étale object over `T` in a chosen big
pro-étale presentation to the same object over `S` along a carrier morphism
`f : T ⟶ S`, inducing functors and adjunctions on sheaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace SmallToBig

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier}

/-- The chosen small pro-étale site of an object has fibre products. -/
theorem smallSite_hasPullbacks (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    HasPullbacks (smallSite X T) :=
  smallSiteHasPullbacks X T

/-- The chosen small pro-étale site of an object has equalizers. -/
theorem smallSite_hasEqualizers (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    HasEqualizers (smallSite X T) :=
  smallSiteHasEqualizers X T

/-- The relocalization functor from the chosen small pro-étale site of `T` to
the chosen big pro-étale slice over `S`. On objects it sends a weakly étale
morphism `j : U ⟶ T` to `j ≫ f : U ⟶ S`. -/
abbrev relocalizationFunctor (f : T ⟶ S) : smallSite X T ⥤ bigSite X S :=
  smallInclusion X T ⋙ Over.map f

/-- The relocalization functor is continuous for the chosen small-to-big
pro-étale topologies. -/
theorem relocalizationFunctor_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (relocalizationFunctor f) (smallTopology X T)
      (bigTopology X S) := sorry

/-- The relocalization functor is cocontinuous for the chosen small-to-big
pro-étale topologies. -/
theorem relocalizationFunctor_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (relocalizationFunctor f) (smallTopology X T)
      (bigTopology X S) := sorry

/-- Chosen pro-étale relocalization preserves fibre products. -/
theorem Relocalization.preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (relocalizationFunctor f) := sorry

/-- Chosen pro-étale relocalization preserves equalizers. -/
theorem Relocalization.preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (relocalizationFunctor f) := sorry

/-- The opposite relocalization functor has the left Kan extensions used by
lower shriek. -/
theorem relocalizationFunctor_op_hasLeftKanExtension
    (f : T ⟶ S) [UnivLE.{max u v, w}] (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := sorry

/-- The opposite relocalization functor has the pointwise left Kan extensions
used by finite-connected-limit preservation of lower shriek. -/
theorem relocalizationFunctor_op_hasPointwiseLeftKanExtension
    (f : T ⟶ S) [UnivLE.{max u v, w}] (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseLeftKanExtension P := sorry

/-- The opposite relocalization functor has the pointwise right Kan extensions
used by the cocontinuous direct image. -/
theorem relocalizationFunctor_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) [UnivLE.{max u v, w}] (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on sheaves induced by chosen pro-étale
relocalization. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (smallTopology X T) (Type w) :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (relocalizationFunctor f) (Type w) _
    (smallTopology X T) (bigTopology X S)
    (relocalizationFunctor_isContinuous f)

/-- The inverse image is computed by evaluating on the same object viewed over
`S`. -/
theorem inverseImage_obj_obj (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X T) :
    ((inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X T) :
    ((inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  @Functor.sheafPushforwardContinuousObjObjIso _ _ _ _ (relocalizationFunctor f)
    (Type w) _ _ _ (relocalizationFunctor_isContinuous f) 𝒢 U

/-- The lower-shriek functor on chosen small-to-big pro-étale sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  @Functor.sheafPullback _ _ _ _ (relocalizationFunctor f) (Type w) _
    (smallTopology X T) (bigTopology X S)
    (relocalizationFunctor_isContinuous f)
    (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (relocalizationFunctor f) (Type w) _ (smallTopology X T) (bigTopology X S)
      (relocalizationFunctor_isContinuous f)
      (relocalizationFunctor_op_hasLeftKanExtension f) inferInstance).isRightAdjoint

/-- Lower shriek along chosen pro-étale relocalization preserves fibre products. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (bigTopology X S) (Type w)] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) :=
  @Functor.SheafPullback.Pullbacks.preservesPullbacks _ _ _ _ _ _
    (relocalizationFunctor f) (relocalizationFunctor_isContinuous f) inferInstance
    (relocalizationFunctor_op_hasPointwiseLeftKanExtension f)
    (smallSite_hasPullbacks X T) (smallSite_hasEqualizers X T)
    (Relocalization.preservesPullbacks f) (Relocalization.preservesEqualizers f)

/-- Lower shriek along chosen pro-étale relocalization preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (bigTopology X S) (Type w)] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) :=
  @Functor.SheafPullback.Pullbacks.preservesEqualizers _ _ _ _ _ _
    (relocalizationFunctor f) (relocalizationFunctor_isContinuous f) inferInstance
    (relocalizationFunctor_op_hasPointwiseLeftKanExtension f)
    (smallSite_hasPullbacks X T) (smallSite_hasEqualizers X T)
    (Relocalization.preservesPullbacks f) (Relocalization.preservesEqualizers f)

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  @Functor.sheafAdjunctionContinuous _ _ _ _ (relocalizationFunctor f) (Type w) _
    (smallTopology X T) (bigTopology X S)
    (relocalizationFunctor_isContinuous f)
    (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (relocalizationFunctor f) (Type w) _ (smallTopology X T) (bigTopology X S)
      (relocalizationFunctor_isContinuous f)
      (relocalizationFunctor_op_hasLeftKanExtension f) inferInstance).isRightAdjoint

/-- The direct-image functor presented by cocontinuous chosen pro-étale
relocalization. -/
abbrev directImage (f : T ⟶ S) [UnivLE.{max u v, w}] :
    Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  @Functor.sheafPushforwardCocontinuous _ _ _ _ (relocalizationFunctor f) (Type w) _
    (smallTopology X T) (bigTopology X S)
    (relocalizationFunctor_isCocontinuous f)
    (relocalizationFunctor_op_hasPointwiseRightKanExtension f)

/-- The relocalization inverse image preserves finite limits. -/
theorem inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by chosen pro-étale
relocalization. -/
noncomputable def morphismOfTopoi (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, u, u, w}
      (bigTopology X S) (smallTopology X T) where
  inverseImageFunctor :=
    ⟨inverseImage f, inverseImage_preservesFiniteLimits f⟩
  pushforward := directImage f
  adjunction :=
    @Functor.sheafAdjunctionCocontinuous _ _ _ _ (relocalizationFunctor f) (Type w) _
      (smallTopology X T) (bigTopology X S)
      (relocalizationFunctor_isCocontinuous f)
      (relocalizationFunctor_op_hasPointwiseRightKanExtension f)
      (relocalizationFunctor_isContinuous f)

/-- The inverse-image projection of the bundled relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)] :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasSheafify (smallTopology X T) (Type w)] :
    (morphismOfTopoi f).pushforward = directImage f := sorry

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite
