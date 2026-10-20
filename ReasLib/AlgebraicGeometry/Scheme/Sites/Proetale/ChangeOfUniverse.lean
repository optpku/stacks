module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Refinement
public import ReasLib.CategoryTheory.Sites.Topos.Retraction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigProetaleSite

variable {X Y : BigProetaleSite.{u}}
variable (incl : X.carrier ⥤ Y.carrier) (e : incl ⋙ Y.toScheme ≅ X.toScheme)

/-- A bounded big pro-étale site has finite limits. -/
theorem hasFiniteLimits (X : BigProetaleSite.{u}) : HasFiniteLimits X.carrier :=
  sorry

/-- A scheme-compatible functor between bounded big pro-étale sites is fully faithful. -/
def inclusionFullyFaithful : incl.FullyFaithful :=
  @Functor.FullyFaithful.ofCompFaithful _ _ _ _ _ _ incl Y.toScheme
    Y.fullyFaithful.faithful (X.fullyFaithful.ofIso e.symm)

include e

/-- A scheme-compatible functor between bounded big pro-étale sites preserves finite limits. -/
theorem inclusion_preservesFiniteLimits : PreservesFiniteLimits incl :=
  sorry

/-- A scheme-compatible functor between bounded big pro-étale sites is continuous. -/
theorem inclusion_isContinuous : incl.IsContinuous X.toGrothendieck Y.toGrothendieck :=
  sorry

/-- A scheme-compatible functor between bounded big pro-étale sites is cocontinuous. -/
theorem inclusion_isCocontinuous : incl.IsCocontinuous X.toGrothendieck Y.toGrothendieck :=
  sorry

/-- Sheaf pullback along a scheme-compatible inclusion of bounded big pro-étale sites
preserves finite limits. -/
theorem inclusion_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ incl (Type u) _ X.toGrothendieck Y.toGrothendieck
        (inclusion_isContinuous incl e)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ incl
          (Type u) _ X.toGrothendieck Y.toGrothendieck
          (inclusion_isContinuous incl e) inferInstance inferInstance).isRightAdjoint) :=
  sorry

/-- The continuous morphism of topoi induced by a scheme-compatible inclusion of bounded
big pro-étale sites. -/
def continuousMorphism : MorphismOfTopoiIn.{u} X.toGrothendieck Y.toGrothendieck :=
  @Functor.morphismOfTopoiInOfContinuous _ _ _ _ incl X.toGrothendieck Y.toGrothendieck
    (inclusion_isContinuous incl e) inferInstance inferInstance
    (inclusion_sheafPullback_preservesFiniteLimits incl e)

/-- The cocontinuous morphism of topoi induced by a scheme-compatible inclusion of bounded
big pro-étale sites. -/
def cocontinuousMorphism : MorphismOfTopoiIn.{u} Y.toGrothendieck X.toGrothendieck :=
  @Functor.morphismOfTopoiInOfCocontinuous _ _ _ _ incl X.toGrothendieck Y.toGrothendieck
    (inclusion_isCocontinuous incl e) inferInstance inferInstance

/-- The continuous and cocontinuous morphisms induced by an inclusion of bounded big
pro-étale sites compose to the identity on inverse images. -/
def inclusion_comp_inverseImageIso :
    (MorphismOfTopoiIn.comp (continuousMorphism incl e)
      (cocontinuousMorphism incl e)).inverseImage ≅
        (MorphismOfTopoiIn.id X.toGrothendieck).inverseImage :=
  @Functor.Retraction.compInverseImageIso _ _ _ _ X.toGrothendieck Y.toGrothendieck incl
    (inclusionFullyFaithful incl e).full (inclusionFullyFaithful incl e).faithful
    (inclusion_isContinuous incl e) (inclusion_isCocontinuous incl e)
    inferInstance inferInstance inferInstance
    (inclusion_sheafPullback_preservesFiniteLimits incl e) inferInstance inferInstance

/-- The functor on slices induced by an inclusion of bounded big pro-étale sites
is continuous. -/
theorem sliceInclusion_isContinuous (S : X.carrier) :
    (Over.post (X := S) incl).IsContinuous (X.toGrothendieck.over S)
      (Y.toGrothendieck.over (incl.obj S)) :=
  sorry

/-- The functor on slices induced by an inclusion of bounded big pro-étale sites
is cocontinuous. -/
theorem sliceInclusion_isCocontinuous (S : X.carrier) :
    (Over.post (X := S) incl).IsCocontinuous (X.toGrothendieck.over S)
      (Y.toGrothendieck.over (incl.obj S)) := by
  have h := inclusion_isCocontinuous incl e
  infer_instance

/-- Sheaf pullback along the slice functor of a bounded big pro-étale inclusion
preserves finite limits. -/
theorem sliceInclusion_sheafPullback_preservesFiniteLimits (S : X.carrier) :
    PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (Over.post (X := S) incl) (Type u) _
        (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
        (sliceInclusion_isContinuous incl e S)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
          (Over.post (X := S) incl) (Type u) _ (X.toGrothendieck.over S)
          (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isContinuous incl e S)
          inferInstance inferInstance).isRightAdjoint) :=
  sorry

/-- The continuous morphism of topoi induced on slices by a bounded big pro-étale inclusion. -/
def sliceContinuousMorphism (S : X.carrier) :
    MorphismOfTopoiIn.{u} (X.toGrothendieck.over S)
      (Y.toGrothendieck.over (incl.obj S)) :=
  @Functor.morphismOfTopoiInOfContinuous _ _ _ _ (Over.post (X := S) incl)
    (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
    (sliceInclusion_isContinuous incl e S) inferInstance inferInstance
    (sliceInclusion_sheafPullback_preservesFiniteLimits incl e S)

/-- The cocontinuous morphism of topoi induced on slices by a bounded big pro-étale inclusion. -/
def sliceCocontinuousMorphism (S : X.carrier) :
    MorphismOfTopoiIn.{u} (Y.toGrothendieck.over (incl.obj S))
      (X.toGrothendieck.over S) :=
  @Functor.morphismOfTopoiInOfCocontinuous _ _ _ _ (Over.post (X := S) incl)
    (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
    (sliceInclusion_isCocontinuous incl e S) inferInstance inferInstance

/-- The continuous and cocontinuous morphisms induced on slices by a bounded big
pro-étale inclusion compose to the identity on inverse images. -/
def sliceInclusion_comp_inverseImageIso (S : X.carrier) :
    (MorphismOfTopoiIn.comp (sliceContinuousMorphism incl e S)
      (sliceCocontinuousMorphism incl e S)).inverseImage ≅
        (MorphismOfTopoiIn.id (X.toGrothendieck.over S)).inverseImage :=
  @Functor.Retraction.overCompInverseImageIso _ _ _ _ X.toGrothendieck Y.toGrothendieck
    incl S (Functor.FullyFaithful.over S incl (inclusionFullyFaithful incl e)).full
    (Functor.FullyFaithful.over S incl (inclusionFullyFaithful incl e)).faithful
    (sliceInclusion_isContinuous incl e S) (sliceInclusion_isCocontinuous incl e S)
    inferInstance inferInstance inferInstance
    (sliceInclusion_sheafPullback_preservesFiniteLimits incl e S) inferInstance inferInstance

end AlgebraicGeometry.BigProetaleSite
