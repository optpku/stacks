/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist

/-!
# Composition of twist-compatible maps of projective spectra

This leaf gives the domain, morphism, and twist-comparison computations for composition of
`ProjMap`s.  It is deliberately separate from construction of a single map so users can import
only the composition/naturality API.
-/

@[expose] public section

open CategoryTheory
open HomogeneousIdeal
open HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B C sigma tau omega : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  [CommRing C] [SetLike omega C] [AddSubgroupClass omega C]
  {calA : Nat -> sigma} {calB : Nat -> tau} {calC : Nat -> omega}
  [GradedRing calA] [GradedRing calB] [GradedRing calC]
  {PcalA : ProjTwistPresentation calA}
  {PcalB : ProjTwistPresentation calB}
  {PcalC : ProjTwistPresentation calC}
  {phi : calA →+*ᵍ calB} {psi : calB →+*ᵍ calC}

namespace ProjMap

/-- The image-open realization of the pullback of the domain of `phi` along a `ProjMap` for
`psi`. -/
@[stacks 01MZ]
abbrev compDomain
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi) : (Proj calC).Opens :=
  (projMapDomain psi).ι ''ᵁ (hpsi.map ⁻¹ᵁ projMapDomain phi)

/-- The restricted composite map on the concrete image-open domain. -/
@[stacks 01MZ]
abbrev compMapOnCompDomain
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi) :
    (compDomain phi hpsi).toScheme ⟶ Proj calA :=
  ((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
    Scheme.Hom.resLE hpsi.map (projMapDomain phi) (hpsi.map ⁻¹ᵁ projMapDomain phi) le_rfl ≫
      hphi.map

/-- The intermediate twist on the concrete composite domain. -/
@[stacks 01MZ]
abbrev compMiddleTwistOnCompDomain
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi)
    (n : Int) :
    (compDomain phi hpsi).toScheme.Modules :=
  (Scheme.Modules.pullback ((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv).obj
      ((Scheme.Modules.pullback
        (Scheme.Hom.resLE hpsi.map (projMapDomain phi) (hpsi.map ⁻¹ᵁ projMapDomain phi) le_rfl)).obj
      ((Scheme.Modules.pullback (projMapDomain phi).ι).obj (PcalB.actualTwist n)))

/-- The intermediate twist transported to an identified copy of the composite domain. -/
abbrev compMiddleTwist
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi)
    {U : (Proj calC).Opens}
    (hdomain : U = compDomain phi hpsi)
    (n : Int) :
    U.toScheme.Modules :=
  (Scheme.Modules.pullback
      (eqToHom (congrArg (fun V : (Proj calC).Opens => V.toScheme) hdomain))).obj
    (compMiddleTwistOnCompDomain phi hpsi n)

/-- The pullback of the first twist comparison to the concrete composite domain. -/
@[stacks 01MZ]
abbrev compPullbackThetaOnCompDomain
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (n : Int) :
    (Scheme.Modules.pullback (compMapOnCompDomain hphi hpsi)).obj (PcalA.actualTwist n) ⟶
      compMiddleTwistOnCompDomain phi hpsi n :=
  ((Scheme.Modules.pullbackComp
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
        Scheme.Hom.resLE hpsi.map (projMapDomain phi) (hpsi.map ⁻¹ᵁ projMapDomain phi) le_rfl)
      hphi.map).inv.app (PcalA.actualTwist n)) ≫
    (Scheme.Modules.pullback
        (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          Scheme.Hom.resLE hpsi.map (projMapDomain phi) (hpsi.map ⁻¹ᵁ projMapDomain phi) le_rfl)).map
      (hphi.theta n) ≫
    ((Scheme.Modules.pullbackComp
        ((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv
        (Scheme.Hom.resLE hpsi.map (projMapDomain phi) (hpsi.map ⁻¹ᵁ projMapDomain phi) le_rfl)).inv.app
      ((Scheme.Modules.pullback (projMapDomain phi).ι).obj (PcalB.actualTwist n)))

/-- The image-open inclusion used in the composite-domain construction. -/
theorem compDomain_isoImage_inv_ι
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi) :
    (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
        (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
      (projMapDomain psi).ι =
    (compDomain phi hpsi).ι := sorry

/-- The second twist comparison on the concrete composite domain. -/
@[stacks 01MZ]
abbrev compThetaPsiOnCompDomain
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι)
    (n : Int) :
    compMiddleTwistOnCompDomain phi hpsi n ⟶
      (Scheme.Modules.pullback (compDomain phi hpsi).ι).obj (PcalC.actualTwist n) :=
  let preimageOpen := hpsi.map ⁻¹ᵁ projMapDomain phi
  let imageIso : (compDomain phi hpsi).toScheme ⟶ preimageOpen.toScheme :=
    ((projMapDomain psi).ι.isoImage preimageOpen).inv
  let restrictedMap : preimageOpen.toScheme ⟶ (projMapDomain phi).toScheme :=
    Scheme.Hom.resLE hpsi.map (projMapDomain phi) preimageOpen le_rfl
  let sourceRestrict :
      (Scheme.Modules.pullback restrictedMap).obj
          ((Scheme.Modules.pullback (projMapDomain phi).ι).obj (PcalB.actualTwist n)) ⟶
        ((Scheme.Modules.pullback hpsi.map).obj (PcalB.actualTwist n)).restrict preimageOpen.ι :=
    ((Scheme.Modules.pullbackComp restrictedMap (projMapDomain phi).ι).hom.app
      (PcalB.actualTwist n)) ≫
      ((Scheme.Modules.pullbackCongr
          (Scheme.Hom.resLE_comp_ι hpsi.map le_rfl)).hom.app (PcalB.actualTwist n)) ≫
      ((Scheme.Modules.pullbackComp preimageOpen.ι hpsi.map).inv.app (PcalB.actualTwist n)) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback preimageOpen.ι).inv.app
        ((Scheme.Modules.pullback hpsi.map).obj (PcalB.actualTwist n)))
  let thetaToRestrict :
      (Scheme.Modules.pullback hpsi.map).obj (PcalB.actualTwist n) ⟶
        (PcalC.actualTwist n).restrict (projMapDomain psi).ι :=
    hpsi.theta n ≫
      ((Scheme.Modules.restrictFunctorIsoPullback (projMapDomain psi).ι).inv.app
        (PcalC.actualTwist n))
  (Scheme.Modules.pullback imageIso).map sourceRestrict ≫
    (Scheme.Modules.pullback imageIso).map
      ((Scheme.Modules.restrictFunctor preimageOpen.ι).map thetaToRestrict) ≫
    ((Scheme.Modules.restrictFunctorIsoPullback imageIso).inv.app
      (((PcalC.actualTwist n).restrict (projMapDomain psi).ι).restrict preimageOpen.ι)) ≫
    ((Scheme.Modules.restrictFunctorComp imageIso preimageOpen.ι).inv.app
      ((PcalC.actualTwist n).restrict (projMapDomain psi).ι)) ≫
    ((Scheme.Modules.restrictFunctorComp
        (imageIso ≫ preimageOpen.ι)
        (projMapDomain psi).ι).inv.app (PcalC.actualTwist n)) ≫
    ((Scheme.Modules.restrictFunctorCongr
        h_image_inclusion).hom.app (PcalC.actualTwist n)) ≫
    ((Scheme.Modules.restrictFunctorIsoPullback (compDomain phi hpsi).ι).hom.app
      (PcalC.actualTwist n))

end ProjMap

/-- The domain of a composite graded map is the pullback of the first domain along the map
induced by the second graded map. -/
@[stacks 01MZ]
theorem projMapDomain_comp
    (hpsi : ProjMap PcalB PcalC psi) :
    projMapDomain (psi.comp phi) = ProjMap.compDomain phi hpsi := sorry

namespace ProjMap

/-- Transport of the image-open inclusion to the actual domain of the composite graded map. -/
theorem compDomain_transport_ι
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi) :
    eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
        (compDomain phi hpsi).ι =
      (projMapDomain (psi.comp phi)).ι := sorry

/-- The second twist comparison transported to the actual domain of the composite map. -/
@[stacks 01MZ]
abbrev compThetaPsi
    (phi : calA →+*ᵍ calB)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι)
    (h_domain_inclusion :
      eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
          (compDomain phi hpsi).ι =
        (projMapDomain (psi.comp phi)).ι)
    (n : Int) :
    compMiddleTwist phi hpsi h_domain n ⟶
      (Scheme.Modules.pullback (projMapDomain (psi.comp phi)).ι).obj (PcalC.actualTwist n) :=
  (Scheme.Modules.pullback
      (eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain))).map
    (compThetaPsiOnCompDomain phi hpsi h_image_inclusion n) ≫
    ((Scheme.Modules.pullbackComp
        (eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain))
        (compDomain phi hpsi).ι).hom.app (PcalC.actualTwist n)) ≫
    ((Scheme.Modules.pullbackCongr h_domain_inclusion).hom.app
      (PcalC.actualTwist n))

/-- The composite map on the actual domain of the composite graded map. -/
@[stacks 01MZ]
abbrev compMap
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi) :
    (projMapDomain (psi.comp phi)).toScheme ⟶ Proj calA :=
  eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
    compMapOnCompDomain hphi hpsi

/-- The pullback of the first twist comparison on the actual composite domain. -/
@[stacks 01MZ]
abbrev compPullbackTheta
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (n : Int) :
    (Scheme.Modules.pullback (compMap hphi hpsi h_domain)).obj (PcalA.actualTwist n) ⟶
      compMiddleTwist phi hpsi h_domain n :=
  ((Scheme.Modules.pullbackComp
      (eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain))
      (compMapOnCompDomain hphi hpsi)).inv.app (PcalA.actualTwist n)) ≫
    (Scheme.Modules.pullback
        (eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain))).map
      (compPullbackThetaOnCompDomain hphi hpsi n)

/-- The composite degreewise twist comparison. -/
@[stacks 01MZ]
abbrev compTheta
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι)
    (h_domain_inclusion :
      eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
          (compDomain phi hpsi).ι =
        (projMapDomain (psi.comp phi)).ι)
    (n : Int) :
    (Scheme.Modules.pullback (compMap hphi hpsi h_domain)).obj (PcalA.actualTwist n) ⟶
      (Scheme.Modules.pullback (projMapDomain (psi.comp phi)).ι).obj (PcalC.actualTwist n) :=
  compPullbackTheta hphi hpsi h_domain n ≫
    compThetaPsi phi hpsi h_domain h_image_inclusion h_domain_inclusion n

/-- The composite comparison maps preserve graded sections, units, and multiplication. -/
theorem comp_theta_compatibility
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι)
    (h_domain_inclusion :
      eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
          (compDomain phi hpsi).ι =
        (projMapDomain (psi.comp phi)).ι) :
    projMapThetaCompatibility PcalA PcalC (psi.comp phi)
      (compMap hphi hpsi h_domain)
      (compTheta hphi hpsi h_domain h_image_inclusion h_domain_inclusion) := sorry

/-- The composite map has the expected inverse images and affine descriptions on basic opens. -/
theorem comp_basicOpen_compatibility
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι) :
    projMapBasicOpenCompatibility (psi.comp phi) (compMap hphi hpsi h_domain) := sorry

/-- The composition of two twist-compatible maps of projective spectra. -/
@[stacks 01MZ]
def comp
    (hphi : ProjMap PcalA PcalB phi)
    (hpsi : ProjMap PcalB PcalC psi)
    (h_domain : projMapDomain (psi.comp phi) = compDomain phi hpsi)
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage (hpsi.map ⁻¹ᵁ projMapDomain phi)).inv ≫
          (hpsi.map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (compDomain phi hpsi).ι)
    (h_domain_inclusion :
      eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
          (compDomain phi hpsi).ι =
        (projMapDomain (psi.comp phi)).ι) :
    ProjMap PcalA PcalC (psi.comp phi) where
  map := compMap hphi hpsi h_domain
  theta := compTheta hphi hpsi h_domain h_image_inclusion h_domain_inclusion
  degree_commutes :=
    (comp_theta_compatibility hphi hpsi h_domain h_image_inclusion h_domain_inclusion).1
  theta_map_one :=
    (comp_theta_compatibility hphi hpsi h_domain h_image_inclusion h_domain_inclusion).2.1
  theta_map_mul :=
    (comp_theta_compatibility hphi hpsi h_domain h_image_inclusion h_domain_inclusion).2.2
  preimage_basicOpen :=
    (comp_basicOpen_compatibility hphi hpsi h_domain h_image_inclusion).1
  basicOpenIsoSpec_inv_comp :=
    (comp_basicOpen_compatibility hphi hpsi h_domain h_image_inclusion).2

end ProjMap

/-- The canonical projective-spectrum map of a composite graded map is the restricted
composition of the two canonical projective-spectrum maps. -/
@[stacks 01MZ]
theorem projMap_comp :
    (h_domain : projMapDomain (psi.comp phi) =
      ProjMap.compDomain phi (projMap PcalB PcalC psi)) →
    (projMap PcalA PcalC (psi.comp phi)).map =
      ProjMap.compMap (projMap PcalA PcalB phi) (projMap PcalB PcalC psi) h_domain := sorry

/-- The canonical twist comparison of a composite graded map is the pullback of the first
canonical comparison followed by the second canonical comparison. -/
@[stacks 01MZ]
theorem projMap_theta_comp :
    (h_domain : projMapDomain (psi.comp phi) =
      ProjMap.compDomain phi (projMap PcalB PcalC psi)) →
    (h_image_inclusion :
      (((projMapDomain psi).ι.isoImage
          ((projMap PcalB PcalC psi).map ⁻¹ᵁ projMapDomain phi)).inv ≫
          ((projMap PcalB PcalC psi).map ⁻¹ᵁ projMapDomain phi).ι) ≫
        (projMapDomain psi).ι =
      (ProjMap.compDomain phi (projMap PcalB PcalC psi)).ι) →
    (h_domain_inclusion :
      eqToHom (congrArg (fun U : (Proj calC).Opens => U.toScheme) h_domain) ≫
          (ProjMap.compDomain phi (projMap PcalB PcalC psi)).ι =
        (projMapDomain (psi.comp phi)).ι) →
    forall n : Int,
      (projMap PcalA PcalC (psi.comp phi)).theta n =
        ((Scheme.Modules.pullbackCongr (projMap_comp h_domain)).hom.app
          (PcalA.actualTwist n)) ≫
          ProjMap.compTheta (projMap PcalA PcalB phi) (projMap PcalB PcalC psi)
            h_domain h_image_inclusion h_domain_inclusion n := sorry

end

end AlgebraicGeometry
