module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfSite.FullyFaithful
import StacksCheckRecall

/-!
# Lemma 94.18.2

Enlarging the chosen big fppf site induces a locally equivalent pseudofunctor
on algebraic stacks. Its essential image is characterized by smooth
presentations whose object and arrow spaces descend to the smaller site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChosenBigFppfSite
open scoped CategoryTheory.Bicategory

universe u v w

variable (𝒮 𝒯 : AlgebraicGeometry.ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
variable [hContinuous : (Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hKan : ∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [hPullbacks : HasPullbacks (Over S)] [hEqualizers : HasEqualizers (Over S)]
variable [hPostPullbacks : PreservesLimitsOfShape WalkingCospan (Over.post (X := S) inclusion)]
variable [hPostEqualizers : PreservesLimitsOfShape WalkingParallelPair
  (Over.post (X := S) inclusion)]

variable [hFull : inclusion.Full] [hFaithful : inclusion.Faithful]
variable [hSubcanonical : (𝒮.bigTopology S).Subcanonical]
variable [hLimits : PreservesLimitsOfShape WalkingCospan inclusion]
variable [hCocontinuous : (Over.post (X := S) inclusion).IsCocontinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hFiniteLimits : PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
variable [hSourceFiniteLimits : HasFiniteLimits (Over S)]
variable [hPostFiniteLimits : PreservesFiniteLimits (Over.post (X := S) inclusion)]
variable [hSmall : Small.{w} (Over (inclusion.obj S))]


/- Lemma 94.18.2 (1): inverse image defines a functor of 2-categories
of algebraic stacks over S and an equivalence on every morphism category. -/
@[stacks 04X3] #check
  (AlgebraicGeometry.ChosenBigFppfSite.exists_inverseImage_locallyEquivalence
    𝒮 S 𝒯 inclusion e :
    ∃ F : Pseudofunctor (AlgebraicStacks.{u, v, w} 𝒮 S)
        (AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S)),
      AlgebraicStacks.IsInverseImage 𝒮 S 𝒯 inclusion F ∧ F.IsLocallyEquivalence)

variable (X' : AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S))

/- Lemma 94.18.2 (2): an algebraic stack on the larger site is equivalent
to an inverse image if and only if it has a smooth presentation [U'/R']
with U' and R' isomorphic to inverse images of smaller-site algebraic spaces. -/
@[stacks 04X3] #check
  (AlgebraicGeometry.ChosenBigFppfSite.essentiallyInImage_iff
    𝒮 S 𝒯 inclusion e X' :
    (∃ (X : AlgebraicStacks.{u, v, w} 𝒮 S)
      (I : StackOver.InverseImage.{_, _, _, _, max u v w, max u v w, max u v w, max u v w}
        (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion)
        (AlgebraicStacks.toStackOver 𝒮 S X)),
      ∃ E : CartesianBasedFunctor I.target.p
        (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) X').p,
        E.toBasedFunctor.IsEquivalence) ↔
      HasSmallSitePresentation 𝒮 S 𝒯 inclusion X')
