module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction

/-!
# Étale restriction and inverse images of sheaves

An étale morphism of algebraic spaces induces a cocontinuous (and continuous) functor of small
étale sites whose associated morphism of topoi is `smallEtaleMorphismOfTopoi`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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

/-- Inverse of cocontinuous extension along `smallEtaleToSpaces X` is restriction along
that inclusion. -/
noncomputable def smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtalePresentationRestriction X) ≅
      (smallEtaleToSpaces X).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) :=
  Adjunction.leftAdjointUniq
    (smallEtalePresentationEquivalence X).symm.toAdjunction
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous` is the unique left adjoint
of cocontinuous extension along `smallEtaleToSpaces X`. -/
theorem smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous_spec
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous X =
      Adjunction.leftAdjointUniq
        (smallEtalePresentationEquivalence X).symm.toAdjunction
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)) :=
  sorry

/-- Restriction along étale postcomposition on spaces étale sites is naturally isomorphic to
cocontinuous sheaf pullback through the sheafification comparison. -/
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

/-- Restriction along étale postcomposition on small étale sites is naturally isomorphic to
cocontinuous sheaf pullback through the sheafification comparison. -/
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

/-- The inverse image of the canonical small étale morphism of topoi is naturally isomorphic
to cocontinuous sheaf pullback along étale postcomposition. -/
noncomputable def smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      (etaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (smallEtaleTopology Y) :=
  let iX := smallEtaleInclusionDirectImage X
  let iY := smallEtaleInclusionDirectImage Y
  let j := etaleRestriction f
  let jSpaces := spacesEtaleRestriction f
  let incX := smallEtaleToSpaces X
  let incY := smallEtaleToSpaces Y
  let restrictIncY :=
    incY.sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let restrictJ :=
    j.sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology X) (smallEtaleTopology Y)
  let restrictJSpaces :=
    jSpaces.sheafPushforwardContinuous (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTopology Y)
  let unitIsoY := (smallEtalePresentationEquivalence Y).unitIso
  -- Local instance justification (required composite witness): `Functor.isContinuous_comp`
  -- is a lemma, not a global instance; `sheafPushforwardContinuousIso` requires continuity
  -- of this displayed composite.
  letI : (j ⋙ incY).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology Y) :=
    Functor.isContinuous_comp j incY (smallEtaleTopology X) (smallEtaleTopology Y)
      (spacesEtaleTopology Y)
  -- Local instance justification (required composite witness): `sheafPushforwardContinuousIso`
  -- also requires continuity of this composite, supplied by the same composition lemma.
  letI : (incX ⋙ jSpaces).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology Y) :=
    Functor.isContinuous_comp incX jSpaces (smallEtaleTopology X) (spacesEtaleTopology X)
      (spacesEtaleTopology Y)
  isoWhiskerLeft iY
      (isoWhiskerRight (spacesEtalePullback_sheafPullbackCocontinuous f) (smallEtalePresentationRestriction X)) ≪≫
    isoWhiskerLeft iY
      (isoWhiskerRight (spacesEtaleRestrictionSheaf_sheafPullbackCocontinuous f).symm (smallEtalePresentationRestriction X)) ≪≫
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

/-- The inverse image of the canonical small étale morphism of topoi is naturally isomorphic
to restriction of sheaves along étale postcomposition. -/
noncomputable def smallEtaleMorphismOfTopoi_etaleRestrictionSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      etaleRestrictionSheaf f (Type (u + 1)) :=
  smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous f ≪≫
    (etaleRestrictionSheaf_sheafPullbackCocontinuous f).symm

/-- The inverse-image identification with restriction is the composite of the canonical
inverse-image comparison with the inverse of the sheafification comparison. -/
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

/-- The section identification is the component of the natural inverse-image comparison
transported along the evaluation equation for restricted sheaves. -/
theorem smallEtaleMorphismOfTopoi_inverseImage_obj_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (U : smallEtaleSite X) :
    smallEtaleMorphismOfTopoi_inverseImage_obj f G U =
      ((sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).mapIso
          ((smallEtaleMorphismOfTopoi_etaleRestrictionSheaf f).app G)).app (Opposite.op U) ≪≫
        eqToIso (etaleRestrictionSheaf_obj_obj f (Type (u + 1)) G U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
