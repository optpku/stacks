/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Standard opens in affine charts of projective spectra

Every standard open in the affine chart determined by a positive-degree homogeneous element is
represented by a positive-degree homogeneous numerator whose projective basic open lies in the
chart.
-/

@[expose] public section

universe uA uσ

namespace AlgebraicGeometry.Proj

variable {A : Type uA} {σ : Type uσ}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A standard open in the affine chart at a positive-degree homogeneous element is represented
by a positive-degree homogeneous numerator whose projective basic open is contained in the
chart. -/
theorem exists_positiveDegree_homogeneous_numerator_of_toSpec_basicOpen
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (g : HomogeneousLocalization.Away 𝒜 f) :
    ∃ (n : ℕ) (hn : 0 < n) (h : A) (hh : h ∈ 𝒜 (n • m)),
      ProjectiveSpectrum.basicOpen 𝒜 h ≤ ProjectiveSpectrum.basicOpen 𝒜 f ∧
        (ProjIsoSpecTopComponent.toSpec 𝒜 f) ⁻¹'
              (PrimeSpectrum.basicOpen g :
                Set (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f))) =
            Subtype.val ⁻¹' (ProjectiveSpectrum.basicOpen 𝒜 h :
              Set (ProjectiveSpectrum 𝒜)) ∧
          g = HomogeneousLocalization.Away.mk 𝒜 f_deg n h hh := sorry

end AlgebraicGeometry.Proj
