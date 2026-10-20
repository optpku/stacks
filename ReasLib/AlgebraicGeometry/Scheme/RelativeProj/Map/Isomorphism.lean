module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.OnTarget
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Affine
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Isomorphism

/-!
# Isomorphism criteria for relative projective-spectrum maps

This file gives the full-domain and isomorphism consequences of eventual degreewise isomorphy
for an affine-compatible relative projective-spectrum map.
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

/-- Eventual isomorphy of the nonnegative graded pieces makes the natural domain of an
affine-compatible relative projective-spectrum map equal to the full source scheme. -/
theorem domain_eq_top_of_eventually_isIso
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))) :
    rφ.domain = ⊤ := sorry

/-- Eventual isomorphy of the nonnegative graded pieces makes the full-source morphism of an
affine-compatible relative projective-spectrum map an isomorphism. -/
theorem mapOnTarget_isIso_of_eventually_isIso
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))) :
    let hTop : rφ.domain = ⊤ :=
      domain_eq_top_of_eventually_isIso P𝒜 Pℬ φ rφ hcompat hφIso
    IsIso (mapOnTarget P𝒜 Pℬ φ rφ hTop) := sorry

/-- Eventual isomorphy of the nonnegative graded pieces makes every full-source integral-twist
comparison of an affine-compatible relative projective-spectrum map an isomorphism. -/
theorem thetaOnTarget_isIso_of_eventually_isIso
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d)))
    (n : ℤ) :
    let hTop : rφ.domain = ⊤ :=
      domain_eq_top_of_eventually_isIso P𝒜 Pℬ φ rφ hcompat hφIso
    let hι : domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫ rφ.domain.ι = 𝟙 Y :=
      domainTopInclusion_comp_ι P𝒜 Pℬ φ rφ hTop
    IsIso (thetaOnTarget P𝒜 Pℬ φ rφ hTop hι n) := sorry

end RelativeProjMap

end

end AlgebraicGeometry
