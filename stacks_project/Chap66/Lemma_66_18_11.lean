/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
import StacksCheckRecall

/-!
# Lemma 66.18.11

An étale morphism of algebraic spaces induces a cocontinuous (and continuous) functor of small
étale sites whose associated morphism of topoi is `smallEtaleMorphismOfTopoi`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.18.11 (1): if `f : X ⟶ Y` is étale, postcomposition
`(φ : U ⟶ X) ↦ (f ∘ φ : U ⟶ Y)` is a cocontinuous functor
`etaleRestriction f : smallEtaleSite X ⥤ smallEtaleSite Y`. -/
@[stacks 03LP] #check etaleRestriction
@[stacks 03LP] #check etaleRestriction_isCocontinuous

#check Functor.morphismOfTopoiInOfCocontinuous

/-- The morphism of topoi of `spacesEtalePullback f` has the same inverse image as the
cocontinuous topos morphism of its left adjoint `spacesEtaleRestriction f`. -/
noncomputable def spacesEtalePullback_sheafPullbackCocontinuous
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ≅
      (spacesEtaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y) :=
  Functor.LeftAdjoint.pullbackIsoCocontinuous
    (spacesEtalePullback f) (spacesEtaleRestriction f)
    (Over.mapPullbackAdj (@Etale S) ⊤ f inferInstance trivial) (Type (u + 1))

/-- `spacesEtalePullback_sheafPullbackCocontinuous` is the left-adjoint comparison of
`Functor.LeftAdjoint.pullbackIsoCocontinuous`. -/
theorem spacesEtalePullback_sheafPullbackCocontinuous_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    spacesEtalePullback_sheafPullbackCocontinuous f =
      Functor.LeftAdjoint.pullbackIsoCocontinuous
        (spacesEtalePullback f) (spacesEtaleRestriction f)
        (Over.mapPullbackAdj (@Etale S) ⊤ f inferInstance trivial) (Type (u + 1)) :=
  sorry

/-- Inverse of cocontinuous extension along `smallEtaleInclusion X` is restriction along
that inclusion. -/
noncomputable def smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleInclusionDirectImage X).inv ≅
      (smallEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) :=
  Adjunction.leftAdjointUniq
    (smallEtaleInclusionDirectImage X).asEquivalence.symm.toAdjunction
    ((smallEtaleInclusion X).sheafAdjunctionCocontinuous (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous` is the unique left adjoint
of cocontinuous extension along `smallEtaleInclusion X`. -/
theorem smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous_spec
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous X =
      Adjunction.leftAdjointUniq
        (smallEtaleInclusionDirectImage X).asEquivalence.symm.toAdjunction
        ((smallEtaleInclusion X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)) :=
  sorry

/-- Restriction along `spacesEtaleRestriction f` is isomorphic to cocontinuous sheaf pullback,
by sheafification of the continuous pushforward comparison of Sites, Lemma 7.21.5. -/
noncomputable def spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (spacesEtaleRestriction f).sheafPushforwardContinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y) ≅
      (spacesEtaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
      ((spacesEtaleRestriction f).sheafPushforwardContinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y))
      (sheafificationNatIso (spacesEtaleTopology X) (Type (u + 1))) ≪≫
    isoWhiskerRight
      ((spacesEtaleRestriction f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) (spacesEtaleTopology X) (spacesEtaleTopology Y))
      (presheafToSheaf (spacesEtaleTopology X) (Type (u + 1)))

/-- `spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous` is the sheafification comparison of
continuous restriction with cocontinuous pullback on the spaces étale sites. -/
theorem spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous f).hom =
      (isoWhiskerLeft
          ((spacesEtaleRestriction f).sheafPushforwardContinuous (Type (u + 1))
            (spacesEtaleTopology X) (spacesEtaleTopology Y))
          (sheafificationNatIso (spacesEtaleTopology X) (Type (u + 1))) ≪≫
        isoWhiskerRight
          ((spacesEtaleRestriction f).sheafPushforwardContinuousCompSheafToPresheafIso
            (Type (u + 1)) (spacesEtaleTopology X) (spacesEtaleTopology Y))
          (presheafToSheaf (spacesEtaleTopology X) (Type (u + 1)))).hom :=
  sorry

/-- Restriction along `etaleRestriction f` is isomorphic to cocontinuous sheaf pullback, by
sheafification of the continuous pushforward comparison of Sites, Lemma 7.21.5. -/
noncomputable def etaleRestrictionSheaf_sheafPullbackCocontinuous
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    etaleRestrictionSheaf f (Type (u + 1)) ≅
      (etaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (smallEtaleTopology Y) :=
  isoWhiskerLeft (etaleRestrictionSheaf f (Type (u + 1)))
      (sheafificationNatIso (smallEtaleTopology X) (Type (u + 1))) ≪≫
    isoWhiskerRight
      ((etaleRestriction f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) (smallEtaleTopology X) (smallEtaleTopology Y))
      (presheafToSheaf (smallEtaleTopology X) (Type (u + 1)))

/-- `etaleRestrictionSheaf_sheafPullbackCocontinuous` is the sheafification comparison of
continuous restriction with cocontinuous pullback. -/
theorem etaleRestrictionSheaf_sheafPullbackCocontinuous_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (etaleRestrictionSheaf_sheafPullbackCocontinuous f).hom =
      (isoWhiskerLeft (etaleRestrictionSheaf f (Type (u + 1)))
          (sheafificationNatIso (smallEtaleTopology X) (Type (u + 1))) ≪≫
        isoWhiskerRight
          ((etaleRestriction f).sheafPushforwardContinuousCompSheafToPresheafIso
            (Type (u + 1)) (smallEtaleTopology X) (smallEtaleTopology Y))
          (presheafToSheaf (smallEtaleTopology X) (Type (u + 1)))).hom :=
  sorry

/-- Lemma 66.18.11 (2): the morphism of topoi `smallEtaleMorphismOfTopoi f` is the morphism of
topoi associated to `etaleRestriction f` in the sense of Sites, Lemma 7.21.1, i.e.
`Functor.morphismOfTopoiInOfCocontinuous`. The inverse image is identified with
`sheafPullbackCocontinuous` of `etaleRestriction f` on sheaves of types. -/
@[stacks 03LP]
noncomputable def smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      (etaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (smallEtaleTopology Y) :=
  let iX := smallEtaleInclusionDirectImage X
  let iY := smallEtaleInclusionDirectImage Y
  let j := etaleRestriction f
  let jSpaces := spacesEtaleRestriction f
  let incX := smallEtaleInclusion X
  let incY := smallEtaleInclusion Y
  let restrictIncY :=
    incY.sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let restrictJ :=
    j.sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology X) (smallEtaleTopology Y)
  let restrictJSpaces :=
    jSpaces.sheafPushforwardContinuous (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTopology Y)
  let unitIsoY := iY.asEquivalence.unitIso
  -- Local instance justification (instance diamond): `sheafPushforwardContinuousIso` is indexed
  -- by the displayed composite of the source square, so it must use this composite continuity
  -- witness rather than an unrelated ambient witness.
  letI : (j ⋙ incY).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology Y) :=
    Functor.isContinuous_comp j incY (smallEtaleTopology X) (smallEtaleTopology Y)
      (spacesEtaleTopology Y)
  -- Local instance justification (instance diamond): same for the spaces-site composite of the
  -- source square.
  letI : (incX ⋙ jSpaces).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology Y) :=
    Functor.isContinuous_comp incX jSpaces (smallEtaleTopology X) (spacesEtaleTopology X)
      (spacesEtaleTopology Y)
  isoWhiskerLeft iY
      (isoWhiskerRight (spacesEtalePullback_sheafPullbackCocontinuous f) iX.inv) ≪≫
    isoWhiskerLeft iY
      (isoWhiskerRight (spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous f).symm iX.inv) ≪≫
    isoWhiskerLeft iY
      (isoWhiskerLeft restrictJSpaces
        (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous X)) ≪≫
    isoWhiskerLeft iY
      (sheafPushforwardContinuousComp incX jSpaces (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
    isoWhiskerLeft iY
      (sheafPushforwardContinuousIso (etaleRestriction_comp_inclusion f).symm (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
    isoWhiskerLeft iY
      (sheafPushforwardContinuousComp j incY (Type (u + 1))
        (smallEtaleTopology X) (smallEtaleTopology Y) (spacesEtaleTopology Y)).symm ≪≫
    associator iY restrictIncY restrictJ ≪≫
    isoWhiskerRight
      (isoWhiskerLeft iY
          (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous Y).symm ≪≫
        unitIsoY.symm)
      restrictJ ≪≫
    leftUnitor restrictJ ≪≫
    etaleRestrictionSheaf_sheafPullbackCocontinuous f

/- Lemma 66.18.11 (3): `etaleRestriction f` is continuous as well, so Sites, Lemma 7.21.5
applies. -/
@[stacks 03LP] #check etaleRestriction_isContinuous

#check Functor.sheafPushforwardContinuousCompSheafToPresheafIso
#check Functor.sheafAdjunctionCocontinuous

/-- Lemma 66.18.11 (4): in particular, inverse image along `smallEtaleMorphismOfTopoi f` is
restriction along `etaleRestriction f`, so sections of
`(smallEtaleMorphismOfTopoi f).inverseImage.obj G` at `U` agree with sections of `G` at
`(etaleRestriction f).obj U`. -/
@[stacks 03LP]
noncomputable def smallEtaleMorphismOfTopoi_etaleRestrictionSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      etaleRestrictionSheaf f (Type (u + 1)) :=
  smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous f ≪≫
    (etaleRestrictionSheaf_sheafPullbackCocontinuous f).symm

/-- `smallEtaleMorphismOfTopoi_etaleRestrictionSheaf` is the Sites, Lemma 7.21.5 comparison of
the inverse-image identification of clause (2). -/
theorem smallEtaleMorphismOfTopoi_etaleRestrictionSheaf_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    smallEtaleMorphismOfTopoi_etaleRestrictionSheaf f =
      smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous f ≪≫
        (etaleRestrictionSheaf_sheafPullbackCocontinuous f).symm :=
  sorry

/-- Sections of the inverse image of `𝒢` along `smallEtaleMorphismOfTopoi f` at `U` are
isomorphic to the sections of `𝒢` at `(etaleRestriction f).obj U`. -/
noncomputable def smallEtaleMorphismOfTopoi_inverseImage_obj
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (U : smallEtaleSite X) :
    ((smallEtaleMorphismOfTopoi f).inverseImage.obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op ((etaleRestriction f).obj U)) :=
  ((sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).mapIso
      ((smallEtaleMorphismOfTopoi_etaleRestrictionSheaf f).app G)).app (Opposite.op U) ≪≫
    eqToIso (etaleRestrictionSheaf_obj_obj f (Type (u + 1)) G U)

/-- The section identification of `smallEtaleMorphismOfTopoi_inverseImage_obj` is the component
of clause (4) transported along `etaleRestrictionSheaf_obj_obj`. -/
theorem smallEtaleMorphismOfTopoi_inverseImage_obj_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (U : smallEtaleSite X) :
    smallEtaleMorphismOfTopoi_inverseImage_obj f G U =
      ((sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).mapIso
          ((smallEtaleMorphismOfTopoi_etaleRestrictionSheaf f).app G)).app (Opposite.op U) ≪≫
        eqToIso (etaleRestrictionSheaf_obj_obj f (Type (u + 1)) G U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
