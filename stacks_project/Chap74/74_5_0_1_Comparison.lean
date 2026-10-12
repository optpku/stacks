/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap66.Lemma_66_18_6
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.«66_18_11_1_Restrict»
public import stacks_project.Chap66.«66_27_0_6_Site»

/-!
# Affine étale comparison for algebraic spaces

The special-cocontinuous inclusion of affine objects in the small étale site of an algebraic
space induces a morphism of ringed topoi from `(X_affine,étale, 𝒪_X restricted)` to
`(X_étale, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Ring-valued sheaves on the affine étale site of an algebraic space compose with the
forgetful functor to types. -/
instance affineEtaleTopology_hasSheafCompose_forget_ringCat
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Type-valued sheafification exists on the affine étale topology of an algebraic space. -/
instance affineEtaleTopology_hasSheafify_type {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify (affineEtaleTopology X) (Type u) :=
  sorry

/-- Type-valued sheaves in universe `u` on the affine étale site of `X` extend along
`affineEtaleInclusion X` by a pointwise right Kan extension. -/
instance affineEtaleInclusion_op_hasPointwiseRightKanExtension_type
    {S : Scheme.{u}} (X : AlgebraicSpace S) (P : (affineEtaleSite X)ᵒᵖ ⥤ Type u) :
    (affineEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The inclusion of affine étale objects, viewed as a functor of the associated ringed
sites. -/
abbrev affineEtaleRingedInclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineRingedSite X ⥤ ringedSite X :=
  affineEtaleInclusion X

/-- The identification of restriction of `𝒪_X` with precomposition along
`affineEtaleInclusion`. -/
def affineEtaleComparison_structurePresheafMap {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleRingedInclusion X).op ⋙ (ringedSite X).structureSheaf.obj ⟶
      (affineRingedSite X).structureSheaf.obj :=
  𝟙 _

/-- The canonical morphism of ringed topoi from the affine étale ringed site of an algebraic
space to its small étale ringed site, induced by `affineEtaleInclusion`. -/
def affineEtaleComparison {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.ToposHom (affineRingedSite X) (ringedSite X) :=
  RingedSite.Cocontinuous.toRingedTopos (affineEtaleRingedInclusion X)
    (affineEtaleComparison_structurePresheafMap X)

/-- The underlying morphism of topoi is the cocontinuous geometric morphism of
`affineEtaleInclusion`. -/
theorem affineEtaleComparison_toTopos {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleComparison X).toTopos =
      (affineEtaleInclusion X).morphismOfTopoiInOfCocontinuous
        (affineEtaleTopology X) (smallEtaleTopology X) :=
  sorry

/-- Inverse image along the affine étale comparison is the sheafified cocontinuous
pullback of `affineEtaleInclusion`. -/
theorem affineEtaleComparison_inverseImage {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleComparison X).toTopos.inverseImage =
      (affineEtaleInclusion X).sheafPullbackCocontinuous (Type u)
        (affineEtaleTopology X) (smallEtaleTopology X) :=
  sorry

/-- Inverse image along the affine étale comparison is canonically isomorphic to
restriction along `affineEtaleInclusion`. -/
def affineEtaleComparison_restrictionIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleComparison X).toTopos.inverseImage ≅
      (affineEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (affineEtaleTopology X) (smallEtaleTopology X) :=
  @asIso _ _ _ _
    (Functor.CocontinuousPullback.comparison.{u} (affineEtaleInclusion X)
      (affineEtaleTopology X) (smallEtaleTopology X))
    (Functor.CocontinuousPullback.comparison.isIso.{u} (affineEtaleInclusion X)
      (affineEtaleTopology X) (smallEtaleTopology X))

/-- The forward map of the restriction isomorphism is the canonical
cocontinuous-to-continuous comparison. -/
theorem affineEtaleComparison_restrictionIso_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleComparison_restrictionIso X).hom =
      Functor.CocontinuousPullback.comparison.{u} (affineEtaleInclusion X)
        (affineEtaleTopology X) (smallEtaleTopology X) :=
  sorry

/-- The affine étale comparison is an equivalence of ringed topoi. -/
instance affineEtaleComparison_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleComparison X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
