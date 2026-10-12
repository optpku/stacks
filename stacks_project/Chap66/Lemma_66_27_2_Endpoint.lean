/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_27_2_ParameterBridge

/-! # The source-specified ringed-topos endpoint at the actual parameter -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]
variable (hcomm : p ≫ f = g ≫ q)

/-- The explicit parameter inverse image is left exact, transported by the constructed iso. -/
instance parameterSiteInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (parameterSiteInverseImage p g f q hcomm) :=
  preservesFiniteLimits_of_natIso (parameterSiteInverseImageIso p g f q hcomm)

/-- The actual 18.22.3 inverse image with its right adjoint. The latter is retained
from the site presentation, with adjunction transported through the constructed comparison. -/
def parameterMorphismOfTopoi :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      ((smallEtaleTopology Y).over (smallEtaleSite.mk q))
      ((smallEtaleTopology X).over (smallEtaleSite.mk p)) where
  inverseImageFunctor := LeftExactFunctor.of (parameterSiteInverseImage p g f q hcomm)
  pushforward := (etaleRelocalizeLocalization p g f q hcomm).toTopos.pushforward
  adjunction := (etaleRelocalizeLocalization p g f q hcomm).toTopos.adjunction.ofNatIsoLeft
    (parameterSiteInverseImageIso p g f q hcomm)

/-- The existing direct-image ring map remains a ring map under the transported adjunction. -/
theorem parameterRingCompatible :
    @Direct.IsRingCompatible
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (parameterMorphismOfTopoi p g f q hcomm)
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImage
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImageForgetIso
      (etaleRelocalizeLocalization p g f q hcomm).directStructureMap := sorry

/-- The ringed 18.22.3 localization at the actual sheaf map `s`, on the original site slices. -/
def parameterRingedHom :
    RingedSite.ToposHom ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @ofDirectImage
    ((ringedSite X).localization (smallEtaleSite.mk p))
    ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
    (parameterMorphismOfTopoi p g f q hcomm)
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImage
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImageForgetIso
    (etaleRelocalizeLocalization p g f q hcomm).directStructureMap
    (parameterRingCompatible p g f q hcomm)

/-- The new ringed-topos inverse image is definitionally the formula at `s` transported
by the specified representable-localization equivalences. -/
theorem parameterRingedHom_inverseImage :
    (parameterRingedHom p g f q hcomm).toTopos.inverseImage =
      (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        ((morphismOfTopoi f).localization (etaleRepresentable (smallEtaleSite.mk q))).inverseImage ⋙
          Over.pullback (etaleRelocalizeParameter p g f q hcomm) ⋙
            (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse := rfl

/-- The comparison on direct images is the identity because that actual right adjoint
was retained; the adjunction and inverse image were changed by the constructed comparison. -/
def parameterTwoIso :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeLocalization p g f q hcomm) (parameterRingedHom p g f q hcomm) where
  homIso := Iso.refl _
  comm := sorry

/-- Representable localization sends the restricted structure object to the slice-product
structure object. This is the same comparison as on all ambient Type-u sheaves. -/
def structureObjectIso (Z : AlgebraicSpace S) (T : smallEtaleSite Z) :
    (etaleSliceEquivalence Z T).functor.obj
        (RingedSite.Hom.underlyingStructureSheaf ((ringedSite Z).localization T)) ≅
      (Over.star (etaleRepresentable T)).obj
        (RingedSite.Hom.underlyingStructureSheaf (ringedSite Z)) :=
  (SubcanonicalSlice.restrictionIsoStar (smallEtaleTopology Z) T).app
    (RingedSite.Hom.underlyingStructureSheaf (ringedSite Z))

/-- Transport of the actual parameter inverse image into the sheaf slice. -/
def parameterForgetIso :
    (parameterRingedHom p g f q hcomm).toTopos.inverseImage ⋙
        (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor ≅
      (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        etaleRelocalizeSliceInverseImage p g f q hcomm :=
  Functor.isoWhiskerLeft
      ((etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        etaleRelocalizeSliceInverseImage p g f q hcomm)
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).counitIso ≪≫ Functor.rightUnitor _

/-- The transported ring structure is the actual 18.22.3 structure map at the same `s`.
This is a compatibility equation for already constructed maps, not an existence specification. -/
theorem parameterRingedHom_structure :
    (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor.map
        (parameterRingedHom p g f q hcomm).underlyingMap ≫
      (structureObjectIso X (smallEtaleSite.mk p)).hom =
    (parameterForgetIso p g f q hcomm).hom.app
        (RingedSite.Hom.underlyingStructureSheaf ((ringedSite Y).localization (smallEtaleSite.mk q))) ≫
      (etaleRelocalizeSliceInverseImage p g f q hcomm).map
        (structureObjectIso Y (smallEtaleSite.mk q)).hom ≫
          etaleRelocalizeSliceStructureMap p g f q hcomm := sorry

end AlgebraicGeometry.AlgebraicSpace.Relocalization
