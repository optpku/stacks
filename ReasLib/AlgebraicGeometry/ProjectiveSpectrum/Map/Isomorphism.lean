/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

/-!
# Isomorphism criteria for maps of projective spectra
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat → sigma} {calB : Nat → tau} [GradedRing calA] [GradedRing calB]
  {PcalA : ProjTwistPresentation calA} {PcalB : ProjTwistPresentation calB}
  {psi : calA →+*ᵍ calB}

/-- Eventual degreewise bijectivity makes the natural domain of a graded projective-spectrum
map equal to the full target. -/
theorem projMapDomain_eq_top_of_eventually_bijective
    (hpsibij : ∃ N : Nat,
      ∀ d : Nat, N ≤ d → Function.Bijective (psi.gradedAddHom d)) :
    projMapDomain psi = ⊤ := sorry

/-- Eventual degreewise bijectivity makes the induced map of full projective spectra an
isomorphism. -/
theorem projMapOnTarget_isIso_of_eventually_bijective
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (hpsibij : ∃ N : Nat,
      ∀ d : Nat, N ≤ d → Function.Bijective (psi.gradedAddHom d)) :
    let hU : projMapDomain psi = ⊤ :=
      projMapDomain_eq_top_of_eventually_bijective hpsibij
    IsIso (projMapOnTarget psi (projMap PcalA PcalB psi).map hU) := sorry

/-- Eventual degreewise bijectivity makes every induced comparison between integral twists an
isomorphism. -/
theorem projMapThetaOnTarget_isIso_of_eventually_bijective
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (hpsibij : ∃ N : Nat,
      ∀ d : Nat, N ≤ d → Function.Bijective (psi.gradedAddHom d))
    (n : Int) :
    let hU : projMapDomain psi = ⊤ :=
      projMapDomain_eq_top_of_eventually_bijective hpsibij
    let hi : projMapDomainTopInclusion psi hU ≫ (projMapDomain psi).ι = 𝟙 (Proj calB) :=
      projMapDomainTopInclusion_comp_ι psi hU
    IsIso (projMapThetaOnTarget psi (PcalA.actualTwist n) (PcalB.actualTwist n)
      (projMap PcalA PcalB psi).map ((projMap PcalA PcalB psi).theta n) hU hi) := sorry

end

end AlgebraicGeometry
