module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.Over.ToposWithPullbacks
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

/-- Postcomposition on chosen big pro-étale slices. On objects it sends `V / T`
to `V / S`. -/
abbrev map (f : T ⟶ S) : bigSite X T ⥤ bigSite X S :=
  Over.map f

/-- Pullback on chosen big pro-étale slices. On objects it sends `U / S` to
`U ×_S T / T`. -/
abbrev pullback (f : T ⟶ S) : bigSite X S ⥤ bigSite X T :=
  Over.Site.WithPullbacks.pullbackFunctor X.hasPullbacks f

/-- The canonical postcomposition-pullback adjunction on chosen big pro-étale
slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) : map f ⊣ pullback f :=
  Over.Site.WithPullbacks.mapPullbackAdjunction X.hasPullbacks f

/-- Postcomposition is continuous for the chosen big pro-étale slice
topologies. -/
theorem map_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (map f) (bigTopology X T) (bigTopology X S) :=
  inferInstanceAs
    ((Over.map f).IsContinuous ((X.toGrothendieck).over T) ((X.toGrothendieck).over S))

/-- Postcomposition is cocontinuous for the chosen big pro-étale slice
topologies. -/
theorem map_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (map f) (bigTopology X T) (bigTopology X S) :=
  inferInstanceAs
    ((Over.map f).IsCocontinuous ((X.toGrothendieck).over T) ((X.toGrothendieck).over S))

/-- Pullback is continuous for the chosen big pro-étale slice topologies. -/
theorem pullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (pullback f) (bigTopology X S) (bigTopology X T) :=
  Over.Site.WithPullbacks.pullbackFunctor_isContinuous X.toGrothendieck X.hasPullbacks f

/-- Postcomposition on chosen big pro-étale slices preserves fibre products. -/
theorem Map.preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (map f) := inferInstance

/-- Postcomposition on chosen big pro-étale slices preserves equalizers. -/
theorem Map.preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (map f) := inferInstance

/-- The inverse-image functor on chosen big pro-étale sheaves. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (bigTopology X T) (Type w) :=
  Over.Site.inverseImage X.toGrothendieck f

/-- The inverse image is computed by evaluating on the postcomposed slice
object. -/
theorem inverseImage_obj_obj (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : bigSite X T) :
    ((inverseImage f).obj 𝒢).obj.obj (op U) =
      𝒢.obj.obj (op ((map f).obj U)) := rfl

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : T ⟶ S)
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : bigSite X T) :
    ((inverseImage f).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  @Functor.sheafPushforwardContinuousObjObjIso _ _ _ _ (map f) (Type w) _
    (bigTopology X T) (bigTopology X S) (map_isContinuous f) 𝒢 U

/-- The direct-image functor presented by the continuous pullback right
adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (pullback f) (Type w) _
    (bigTopology X S) (bigTopology X T) (pullback_isContinuous f)

/-- The direct image on chosen big pro-étale sheaves is continuous restriction along pullback. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w) :=
  continuousDirectImage f

/-- The continuous direct image is computed by evaluation on the pullback slice
object. -/
theorem continuousDirectImage_obj_obj (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((continuousDirectImage f).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((pullback f).obj U)) := rfl

/-- The continuous direct-image computation as a canonical objectwise
isomorphism. -/
noncomputable def continuousDirectImage_objObjIso (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((continuousDirectImage f).obj ℱ).obj.obj (op U) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  @Functor.sheafPushforwardContinuousObjObjIso _ _ _ _ (pullback f) (Type w) _
    (bigTopology X S) (bigTopology X T) (pullback_isContinuous f) ℱ U

/-- The cocontinuous direct image is objectwise identified with evaluation on
the pullback slice object. -/
noncomputable def directImage_objObjIso (f : T ⟶ S)
    (ℱ : Sheaf (bigTopology X T) (Type w)) (U : bigSite X S) :
    ((directImage f).obj ℱ).obj.obj (op U) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  continuousDirectImage_objObjIso f ℱ U

/-- Direct image agrees with its continuous pullback presentation. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage.{u, v, w} f ≅ continuousDirectImage f :=
  Iso.refl _

/-- Direct image agrees with cocontinuous pushforward along postcomposition. -/
noncomputable def directImageIsoCocontinuousPresentation (f : T ⟶ S) :
    directImage.{u, v, max u v w} f ≅
      Over.Site.directImage X.toGrothendieck f :=
  @Functor.ContinuousRightAdjoint.pushforwardContinuousIso _ _ _ _
    (bigTopology X T) (bigTopology X S) (map f) (pullback f)
    (Type (max u v w)) _ (mapPullbackAdjunction f)
    (pullback_isContinuous f) (map_isCocontinuous f) inferInstance

/-- Inverse image agrees with sheaf pullback along the continuous slice pullback functor. -/
noncomputable def inverseImageIsoPullbackPresentation (f : T ⟶ S) :
    inverseImage.{u, v, max u v w} f ≅
      Functor.sheafPullbackConstruction.sheafPullback (pullback f)
        (Type (max u v w)) (bigTopology X S) (bigTopology X T) :=
  Adjunction.leftAdjointUniq
    (@Adjunction.sheafPushforwardContinuous _ _ _ _ (Type (max u v w)) _ _ _
      (mapPullbackAdjunction f) (bigTopology X T) (bigTopology X S)
      (map_isContinuous f) (pullback_isContinuous f))
    (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (pullback f) (Type (max u v w)) _ (bigTopology X S) (bigTopology X T)
      (pullback_isContinuous f) inferInstance inferInstance)

/-- The inverse image on chosen big pro-étale sheaves preserves finite
limits. -/
theorem inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by chosen big pro-étale
postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn.{max u v, max u v, u, u, w}
      (bigTopology X S) (bigTopology X T) where
  inverseImageFunctor := ⟨inverseImage f, inverseImage_preservesFiniteLimits f⟩
  pushforward := directImage f
  adjunction :=
    @Adjunction.sheafPushforwardContinuous _ _ _ _ (Type w) _ _ _
      (mapPullbackAdjunction f) (bigTopology X T) (bigTopology X S)
      (map_isContinuous f) (pullback_isContinuous f)

/-- The inverse-image projection of the bundled chosen big pro-étale
morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := rfl

/-- The direct-image projection of the bundled chosen big pro-étale
morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := rfl

/-- Lower shriek on chosen big pro-étale sheaves is sheafified left Kan extension. -/
abbrev lowerShriek (f : T ⟶ S) :
    Sheaf (bigTopology X T) (Type (max u v w)) ⥤
      Sheaf (bigTopology X S) (Type (max u v w)) :=
  Over.Site.lowerShriek X.toGrothendieck f

/-- Lower shriek is left adjoint to inverse image on chosen big pro-étale sheaves. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S) :
    lowerShriek.{u, v, w} f ⊣ inverseImage f :=
  Over.Site.LowerShriek.adjunction X.toGrothendieck f

/-- Lower shriek on chosen big pro-étale sheaves preserves fibre products. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek.{u, v, w} f) :=
  Over.Site.WithPullbacks.LowerShriek.preservesPullbacks
    X.toGrothendieck X.hasPullbacks f

/-- Lower shriek on chosen big pro-étale sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek.{u, v, w} f) :=
  Over.Site.WithPullbacks.LowerShriek.preservesEqualizers
    X.toGrothendieck X.hasPullbacks f

end Big
end AlgebraicGeometry.ChosenBigProetaleSite
