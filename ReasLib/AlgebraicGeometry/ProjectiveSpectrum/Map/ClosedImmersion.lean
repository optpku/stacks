module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist

/-!
# Closed-immersion criteria for maps of projective spectra
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]
  {PcalA : ProjTwistPresentation calA} {PcalB : ProjTwistPresentation calB}
  {psi : calA →+*ᵍ calB}

/-- The canonical map from the full target projective spectrum to the natural map domain when
that domain is known to be top. -/
abbrev projMapDomainTopInclusion
    (psi : calA →+*ᵍ calB) (hU : projMapDomain psi = ⊤) :
    Proj calB ⟶ (projMapDomain psi).toScheme :=
  (Scheme.topIso (Proj calB)).inv ≫ ((Proj calB).isoOfEq hU.symm).hom

/-- The top-domain inclusion is inverse to the canonical inclusion of the natural map domain. -/
theorem projMapDomainTopInclusion_comp_ι
    (psi : calA →+*ᵍ calB) (hU : projMapDomain psi = ⊤) :
    projMapDomainTopInclusion psi hU ≫ (projMapDomain psi).ι = 𝟙 (Proj calB) := sorry

/-- A map from the natural domain of a graded projective-spectrum map extends to the full target
when that natural domain is top. -/
abbrev projMapOnTarget
    (psi : calA →+*ᵍ calB)
    (r : (projMapDomain psi).toScheme ⟶ Proj calA)
    (hU : projMapDomain psi = ⊤) :
    Proj calB ⟶ Proj calA :=
  projMapDomainTopInclusion psi hU ≫ r

/-- A module comparison over the natural domain of a graded projective-spectrum map extends to
the full target when the domain inclusion has an explicit inverse. -/
abbrev projMapThetaOnTarget
    (psi : calA →+*ᵍ calB)
    (FA : (Proj calA).Modules) (FB : (Proj calB).Modules)
    (r : (projMapDomain psi).toScheme ⟶ Proj calA)
    (theta : (Scheme.Modules.pullback r).obj FA ⟶
      (Scheme.Modules.pullback (projMapDomain psi).ι).obj FB)
    (hU : projMapDomain psi = ⊤)
    (hi : projMapDomainTopInclusion psi hU ≫ (projMapDomain psi).ι = 𝟙 (Proj calB)) :
    (Scheme.Modules.pullback (projMapOnTarget psi r hU)).obj FA ⟶ FB :=
  ((Scheme.Modules.pullbackComp (projMapDomainTopInclusion psi hU) r).inv.app FA) ≫
    (Scheme.Modules.pullback (projMapDomainTopInclusion psi hU)).map theta ≫
      ((Scheme.Modules.pullbackComp (projMapDomainTopInclusion psi hU)
        (projMapDomain psi).ι).hom.app FB) ≫
        ((Scheme.Modules.pullbackCongr hi).hom.app FB) ≫
          ((Scheme.Modules.pullbackId (Proj calB)).hom.app FB)

/-- Eventual degreewise surjectivity makes the natural domain of a graded projective-spectrum
map equal to the full target. -/
theorem projMapDomain_eq_top_of_eventually_surjective
    (hpsisurj : Exists fun N : Nat =>
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d)) :
    projMapDomain psi = ⊤ := by
  classical
  obtain ⟨N, hN⟩ := hpsisurj
  apply top_unique
  intro x _
  by_contra hx
  have hmap (f : PositiveHomogeneous calA) : psi f.val ∈ x.asHomogeneousIdeal := by
    by_contra hf
    exact hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨f, hf⟩)
  apply x.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant calB).toAddSubmonoid ≤
    x.asHomogeneousIdeal.toAddSubmonoid
  rw [HomogeneousIdeal.irrelevant_eq_iSup]
  refine iSup₂_le fun j hj ↦ ?_
  intro b hb
  change b ∈ calB j at hb
  have hdegree : N ≤ j * (N + 1) := by
    have := Nat.mul_le_mul_right (N + 1) hj
    omega
  obtain ⟨a, ha⟩ := hN (j * (N + 1)) hdegree
    ⟨b ^ (N + 1), by simpa [nsmul_eq_mul, Nat.mul_comm] using
      SetLike.pow_mem_graded (N + 1) hb⟩
  have hmem := hmap ⟨a.1, j * (N + 1), Nat.mul_pos hj (Nat.succ_pos N), a.2⟩
  have he : psi a.1 = b ^ (N + 1) := congrArg Subtype.val ha
  rw [he] at hmem
  exact x.isPrime.mem_of_pow_mem (N + 1) hmem

/-- Eventual degreewise surjectivity makes the induced map of full projective spectra a closed
immersion. -/
theorem projMap_isClosedImmersion_of_eventually_surjective
    (hpsisurj : Exists fun N : Nat =>
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d)) :
    let hU : projMapDomain psi = ⊤ := projMapDomain_eq_top_of_eventually_surjective hpsisurj
    IsClosedImmersion (projMapOnTarget psi (projMap PcalA PcalB psi).map hU) := sorry

/-- Eventual degreewise surjectivity makes every induced comparison between integral twists an
epimorphism. -/
theorem projMap_theta_epi_of_eventually_surjective
    (hpsisurj : Exists fun N : Nat =>
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d))
    (n : Int) :
    let hU : projMapDomain psi = ⊤ := projMapDomain_eq_top_of_eventually_surjective hpsisurj
    let hi : projMapDomainTopInclusion psi hU ≫ (projMapDomain psi).ι = 𝟙 (Proj calB) :=
      projMapDomainTopInclusion_comp_ι psi hU
    Epi (projMapThetaOnTarget psi (PcalA.actualTwist n) (PcalB.actualTwist n)
      (projMap PcalA PcalB psi).map ((projMap PcalA PcalB psi).theta n) hU hi) := sorry

namespace ProjMap

/-- If a graded ring map is eventually degreewise surjective and its source is generated in
degree one over degree zero, then every induced comparison between integral twists on the full
target projective spectrum is an isomorphism. -/
theorem thetaOnTarget_isIso_of_degreeOneGenerated
    (PcalA : ProjTwistPresentation calA) (PcalB : ProjTwistPresentation calB)
    (hpsisurj : Exists fun N : Nat =>
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d))
    (hgenerated : Algebra.adjoin (calA 0) (calA 1 : Set A) = ⊤)
    (n : Int) :
    let hU : projMapDomain psi = ⊤ := projMapDomain_eq_top_of_eventually_surjective hpsisurj
    let hi : projMapDomainTopInclusion psi hU ≫ (projMapDomain psi).ι = 𝟙 (Proj calB) :=
      projMapDomainTopInclusion_comp_ι psi hU
    IsIso (projMapThetaOnTarget psi (PcalA.actualTwist n) (PcalB.actualTwist n)
      (projMap PcalA PcalB psi).map ((projMap PcalA PcalB psi).theta n) hU hi) := sorry

end ProjMap

end

end AlgebraicGeometry
