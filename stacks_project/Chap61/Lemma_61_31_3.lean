module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChangeOfUniverse
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Cohomology.ChangeOfUniverse
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable {X Y : BigProetaleSite.{u}}
variable (incl : X.carrier ⥤ Y.carrier) (e : incl ⋙ Y.toScheme ≅ X.toScheme)

/- Lemma 61.31.3. An inclusion of bounded big pro-étale sites induces a retraction
of topoi, globally and over every object of the smaller site. -/
@[stacks 0F4S] #check
  (AlgebraicGeometry.BigProetaleSite.inclusion_comp_inverseImageIso incl e :
    (MorphismOfTopoiIn.comp
      (BigProetaleSite.continuousMorphism incl e)
      (BigProetaleSite.cocontinuousMorphism incl e)).inverseImage ≅
        (MorphismOfTopoiIn.id X.toGrothendieck).inverseImage)

variable (S : X.carrier)

#check (AlgebraicGeometry.BigProetaleSite.sliceInclusion_comp_inverseImageIso incl e S :
    (MorphismOfTopoiIn.comp
      (BigProetaleSite.sliceContinuousMorphism incl e S)
      (BigProetaleSite.sliceCocontinuousMorphism incl e S)).inverseImage ≅
        (MorphismOfTopoiIn.id (X.toGrothendieck.over S)).inverseImage)

#check (AlgebraicGeometry.BigProetaleSite.inclusionFullyFaithful incl e : incl.FullyFaithful)
#check (AlgebraicGeometry.BigProetaleSite.inclusion_isContinuous incl e :
  incl.IsContinuous X.toGrothendieck Y.toGrothendieck)
#check (AlgebraicGeometry.BigProetaleSite.inclusion_isCocontinuous incl e :
  incl.IsCocontinuous X.toGrothendieck Y.toGrothendieck)
#check (AlgebraicGeometry.BigProetaleSite.hasFiniteLimits X : HasFiniteLimits X.carrier)
#check (AlgebraicGeometry.BigProetaleSite.hasFiniteLimits Y : HasFiniteLimits Y.carrier)
#check (AlgebraicGeometry.BigProetaleSite.inclusion_preservesFiniteLimits incl e :
  PreservesFiniteLimits incl)

-- In particular, terminal objects and pullbacks are preserved.
#check ((BigProetaleSite.inclusion_preservesFiniteLimits incl e).preservesFiniteLimits
    (Discrete PEmpty) : PreservesLimitsOfShape (Discrete PEmpty) incl)
#check ((BigProetaleSite.inclusion_preservesFiniteLimits incl e).preservesFiniteLimits
    WalkingCospan : PreservesLimitsOfShape WalkingCospan incl)

#check (CategoryTheory.Functor.FullyFaithful.over S incl
    (BigProetaleSite.inclusionFullyFaithful incl e) :
  (Over.post (X := S) incl).FullyFaithful)
#check (AlgebraicGeometry.BigProetaleSite.sliceInclusion_isContinuous incl e S :
  (Over.post (X := S) incl).IsContinuous (X.toGrothendieck.over S)
    (Y.toGrothendieck.over (incl.obj S)))
#check (AlgebraicGeometry.BigProetaleSite.sliceInclusion_isCocontinuous incl e S :
  (Over.post (X := S) incl).IsCocontinuous (X.toGrothendieck.over S)
    (Y.toGrothendieck.over (incl.obj S)))
#check (@CategoryTheory.Over.hasFiniteLimits _ _ S
    (@hasFiniteWidePullbacks_of_hasFiniteLimits _ _ (BigProetaleSite.hasFiniteLimits X)) :
  HasFiniteLimits (Over S))
#check (@CategoryTheory.Over.hasFiniteLimits _ _ (incl.obj S)
    (@hasFiniteWidePullbacks_of_hasFiniteLimits _ _ (BigProetaleSite.hasFiniteLimits Y)) :
  HasFiniteLimits (Over (incl.obj S)))
#check (@CategoryTheory.Limits.PreservesFiniteLimits.overPost _ _ _ _ S incl
    (BigProetaleSite.inclusion_preservesFiniteLimits incl e) :
  PreservesFiniteLimits (Over.post (X := S) incl))
#check ((@CategoryTheory.Limits.PreservesFiniteLimits.overPost _ _ _ _ S incl
    (BigProetaleSite.inclusion_preservesFiniteLimits incl e)).preservesFiniteLimits
    (Discrete PEmpty) :
  PreservesLimitsOfShape (Discrete PEmpty) (Over.post (X := S) incl))
#check ((@CategoryTheory.Limits.PreservesFiniteLimits.overPost _ _ _ _ S incl
    (BigProetaleSite.inclusion_preservesFiniteLimits incl e)).preservesFiniteLimits
    WalkingCospan :
  PreservesLimitsOfShape WalkingCospan (Over.post (X := S) incl))
