/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.OnTarget
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Affine
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

/-!
# Closed-immersion criteria for relative projective-spectrum maps

This file gives the full-domain, closed-immersion, and twist-epimorphism consequences of
eventual degreewise epimorphy for an affine-compatible relative projective-spectrum map.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}
variable (P𝒜 : RelativeProjPresentation pX)
variable (Pℬ : RelativeProjPresentation pY)
variable (φ : P𝒜.algebra ⟶ Pℬ.algebra)

namespace RelativeProjMap

/-- Eventual epimorphy of the nonnegative graded pieces makes the natural domain of an
affine-compatible relative projective-spectrum map equal to the full source scheme. -/
theorem domain_eq_top_of_eventually_surjective
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) :
    rφ.domain = ⊤ := sorry

/-- Eventual epimorphy of the nonnegative graded pieces makes the full-source morphism of an
affine-compatible relative projective-spectrum map a closed immersion. -/
theorem mapOnTarget_isClosedImmersion_of_eventually_surjective
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) :
    let hTop : rφ.domain = ⊤ :=
      domain_eq_top_of_eventually_surjective P𝒜 Pℬ φ rφ hcompat hφsurj
    IsClosedImmersion (mapOnTarget P𝒜 Pℬ φ rφ hTop) := sorry

/-- Eventual epimorphy of the nonnegative graded pieces makes every full-source integral-twist
comparison of an affine-compatible relative projective-spectrum map an epimorphism. -/
theorem thetaOnTarget_epi_of_eventually_surjective
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d)))
    (n : ℤ) :
    let hTop : rφ.domain = ⊤ :=
      domain_eq_top_of_eventually_surjective P𝒜 Pℬ φ rφ hcompat hφsurj
    let hι : domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫ rφ.domain.ι = 𝟙 Y :=
      domainTopInclusion_comp_ι P𝒜 Pℬ φ rφ hTop
    Epi (thetaOnTarget P𝒜 Pℬ φ rφ hTop hι n) := sorry

end RelativeProjMap

end

end AlgebraicGeometry
