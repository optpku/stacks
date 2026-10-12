/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

variable {A B C σ τ ω : Type u}
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ω C] [AddSubgroupClass ω C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (P𝒜 : AlgebraicGeometry.ProjTwistPresentation 𝒜)
  (Pℬ : AlgebraicGeometry.ProjTwistPresentation ℬ)
  (P𝒞 : AlgebraicGeometry.ProjTwistPresentation 𝒞)
  (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (n : ℤ)

/- Lemma 27.11.2: for composable graded ring maps, the natural domain of the composite is the
inverse image of the first domain under the second map; the canonical restricted maps compose;
and the canonical twist comparisons compose degreewise. -/
@[stacks 01MZ] #check
  (AlgebraicGeometry.projMapDomain_comp
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) :
    AlgebraicGeometry.projMapDomain (ψ.comp φ) =
      AlgebraicGeometry.ProjMap.compDomain φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))

#check
  (AlgebraicGeometry.projMap_comp
      (PcalA := P𝒜) (PcalB := Pℬ) (PcalC := P𝒞) (phi := φ) (psi := ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) :
    (AlgebraicGeometry.projMap P𝒜 P𝒞 (ψ.comp φ)).map =
      AlgebraicGeometry.ProjMap.compMap
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))

#check
  (AlgebraicGeometry.projMap_theta_comp
      (PcalA := P𝒜) (PcalB := Pℬ) (PcalC := P𝒞) (phi := φ) (psi := ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι φ
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_transport_ι
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) :
    ∀ n : ℤ,
      (AlgebraicGeometry.projMap P𝒜 P𝒞 (ψ.comp φ)).theta n =
        ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.projMap_comp
            (PcalA := P𝒜) (PcalB := Pℬ) (PcalC := P𝒞)
            (phi := φ) (psi := ψ)
            (AlgebraicGeometry.projMapDomain_comp
              (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))).hom.app (P𝒜.actualTwist n)) ≫
          AlgebraicGeometry.ProjMap.compTheta
            (AlgebraicGeometry.projMap P𝒜 Pℬ φ)
            (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
            (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
            (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι φ
              (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
            (AlgebraicGeometry.ProjMap.compDomain_transport_ι
              (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
              (AlgebraicGeometry.projMapDomain_comp
                (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) n)

#check
  (AlgebraicGeometry.ProjMap.compDomain φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) :
    (AlgebraicGeometry.Proj 𝒞).Opens)

#check
  (AlgebraicGeometry.ProjMap.compMapOnCompDomain
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) :
    (AlgebraicGeometry.ProjMap.compDomain φ
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)).toScheme ⟶
        AlgebraicGeometry.Proj 𝒜)

#check
  (AlgebraicGeometry.ProjMap.compMiddleTwistOnCompDomain
      φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) n :
    (AlgebraicGeometry.ProjMap.compDomain φ
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)).toScheme.Modules)

#check
  (AlgebraicGeometry.ProjMap.compMiddleTwist φ
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) n :
    (AlgebraicGeometry.projMapDomain (ψ.comp φ)).toScheme.Modules)

#check
  (AlgebraicGeometry.ProjMap.compPullbackThetaOnCompDomain
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) n :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.ProjMap.compMapOnCompDomain
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ)
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))).obj (P𝒜.actualTwist n) ⟶
      AlgebraicGeometry.ProjMap.compMiddleTwistOnCompDomain
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) n)

#check
  (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
      (PcalB := Pℬ) (PcalC := P𝒞) (psi := ψ) φ :
    ∀ hψ : AlgebraicGeometry.ProjMap Pℬ P𝒞 ψ,
      (((AlgebraicGeometry.projMapDomain ψ).ι.isoImage
            (hψ.map ⁻¹ᵁ projMapDomain φ)).inv ≫
          (hψ.map ⁻¹ᵁ projMapDomain φ).ι) ≫
        (AlgebraicGeometry.projMapDomain ψ).ι =
          (AlgebraicGeometry.ProjMap.compDomain φ hψ).ι)

#check
  (AlgebraicGeometry.ProjMap.compThetaPsiOnCompDomain
      φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) n :
    AlgebraicGeometry.ProjMap.compMiddleTwistOnCompDomain
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ) n ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.ProjMap.compDomain φ
          (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)).ι).obj (P𝒞.actualTwist n))

#check
  (AlgebraicGeometry.ProjMap.compDomain_transport_ι
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) :
    eqToHom (congrArg
        (fun U : (AlgebraicGeometry.Proj 𝒞).Opens => U.toScheme)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) ≫
      (AlgebraicGeometry.ProjMap.compDomain φ
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)).ι =
      (AlgebraicGeometry.projMapDomain (ψ.comp φ)).ι)

#check
  (AlgebraicGeometry.ProjMap.compThetaPsi φ
      (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_transport_ι
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) n :
    AlgebraicGeometry.ProjMap.compMiddleTwist φ
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) n ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.projMapDomain (ψ.comp φ)).ι).obj (P𝒞.actualTwist n))

#check
  (AlgebraicGeometry.ProjMap.compMap
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) :
    (AlgebraicGeometry.projMapDomain (ψ.comp φ)).toScheme ⟶ AlgebraicGeometry.Proj 𝒜)

#check
  (AlgebraicGeometry.ProjMap.compPullbackTheta
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) n :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.ProjMap.compMap
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp
          (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))).obj (P𝒜.actualTwist n) ⟶
      AlgebraicGeometry.ProjMap.compMiddleTwist φ
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) n)

#check
  (AlgebraicGeometry.ProjMap.compTheta
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_transport_ι
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) n :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.ProjMap.compMap
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp
          (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))).obj (P𝒜.actualTwist n) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.projMapDomain (ψ.comp φ)).ι).obj (P𝒞.actualTwist n))

#check
  (AlgebraicGeometry.ProjMap.comp_theta_compatibility
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_transport_ι
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) :
    AlgebraicGeometry.ProjMap.projMapThetaCompatibility P𝒜 P𝒞 (ψ.comp φ)
      (AlgebraicGeometry.ProjMap.compMap
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))
      (AlgebraicGeometry.ProjMap.compTheta
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
        (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
          φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
        (AlgebraicGeometry.ProjMap.compDomain_transport_ι
          (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
          (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)))))

#check
  (AlgebraicGeometry.ProjMap.comp_basicOpen_compatibility
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)) :
    AlgebraicGeometry.ProjMap.projMapBasicOpenCompatibility (ψ.comp φ)
      (AlgebraicGeometry.ProjMap.compMap
        (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))))

#check
  (AlgebraicGeometry.ProjMap.comp
      (AlgebraicGeometry.projMap P𝒜 Pℬ φ) (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
      (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_isoImage_inv_ι
        φ (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))
      (AlgebraicGeometry.ProjMap.compDomain_transport_ι
        (AlgebraicGeometry.projMap Pℬ P𝒞 ψ)
        (AlgebraicGeometry.projMapDomain_comp (AlgebraicGeometry.projMap Pℬ P𝒞 ψ))) :
    AlgebraicGeometry.ProjMap P𝒜 P𝒞 (ψ.comp φ))
