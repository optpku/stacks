module

public import stacks_project.Chap61.Definition_61_12_8_Presentation
public import stacks_project.Chap61.Lemma_61_12_10_Limits
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Small-to-big pro-étale relocalization on a chosen site

This leaf owns the reusable site and sheaf API for the functor sending a
weakly étale object over `T` in a chosen big pro-étale presentation to the
same object over `S` along a carrier morphism `f : T ⟶ S`.
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
instance smallSite_hasPullbacks (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    HasPullbacks (smallSite X T) :=
  smallSiteHasPullbacks X T

/-- The chosen small pro-étale site of an object has equalizers. -/
instance smallSite_hasEqualizers (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    HasEqualizers (smallSite X T) :=
  smallSiteHasEqualizers X T

/-- The relocalization functor from the chosen small pro-étale site of `T` to
the chosen big pro-étale slice over `S`. On objects it sends a weakly étale
morphism `j : U ⟶ T` to `j ≫ f : U ⟶ S`. -/
abbrev relocalizationFunctor (f : T ⟶ S) : smallSite X T ⥤ bigSite X S :=
  smallInclusion X T ⋙ Over.map f

/-- The relocalization functor is continuous for the chosen small-to-big
pro-étale topologies. -/
instance relocalizationFunctor_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (relocalizationFunctor f) (smallTopology X T)
      (bigTopology X S) := sorry

/-- The relocalization functor is cocontinuous for the chosen small-to-big
pro-étale topologies. -/
instance relocalizationFunctor_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (relocalizationFunctor f) (smallTopology X T)
      (bigTopology X S) := sorry

/-- Chosen pro-étale relocalization preserves fibre products. -/
instance Relocalization.preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (relocalizationFunctor f) := sorry

/-- Chosen pro-étale relocalization preserves equalizers. -/
instance Relocalization.preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (relocalizationFunctor f) := sorry

/-- The opposite relocalization functor has the left Kan extensions used by
lower shriek. -/
instance relocalizationFunctor_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := sorry

/-- The opposite relocalization functor has the pointwise left Kan extensions
used by finite-connected-limit preservation of lower shriek. -/
instance relocalizationFunctor_op_hasPointwiseLeftKanExtension
    (f : T ⟶ S) (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseLeftKanExtension P := sorry

/-- The opposite relocalization functor has the pointwise right Kan extensions
used by the cocontinuous direct image. -/
instance relocalizationFunctor_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (smallSite X T)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on sheaves induced by chosen pro-étale
relocalization. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (smallTopology X T) (Type w) :=
  (relocalizationFunctor f).sheafPushforwardContinuous (Type w)
    (smallTopology X T) (bigTopology X S)

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
  Functor.sheafPushforwardContinuousObjObjIso (relocalizationFunctor f) (Type w) 𝒢 U

/-- The lower-shriek functor on chosen small-to-big pro-étale sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  (relocalizationFunctor f).sheafPullback (Type w)
    (smallTopology X T) (bigTopology X S)

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
    (smallTopology X T) (bigTopology X S)

/-- The direct-image functor presented by cocontinuous chosen pro-étale
relocalization. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous (Type w)
    (smallTopology X T) (bigTopology X S)

/-- The relocalization inverse image preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by chosen pro-étale
relocalization. -/
noncomputable def morphismOfTopoi (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, v, v, w}
      (bigTopology X S) (smallTopology X T) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (relocalizationFunctor f).sheafAdjunctionCocontinuous (Type w)
      (smallTopology X T) (bigTopology X S)

/-- The inverse-image projection of the bundled relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)] :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)] :
    (morphismOfTopoi f).pushforward = directImage f := sorry

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite
