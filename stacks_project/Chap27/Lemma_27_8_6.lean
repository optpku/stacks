module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.StandardOpen
import StacksCheckRecall

@[expose] public section

universe uA uσ

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 27.8.6: every standard open in the affine chart determined by a positive-degree
homogeneous element is induced by a contained projective standard open, and its defining element
has a positive-power homogeneous numerator. -/
@[stacks 01MA] #check
  (AlgebraicGeometry.Proj.exists_positiveDegree_homogeneous_numerator_of_toSpec_basicOpen 𝒜 :
    ∀ {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m), 0 < m →
      (g : HomogeneousLocalization.Away 𝒜 f) →
        ∃ (n : ℕ) (hn : 0 < n) (h : A) (hh : h ∈ 𝒜 (n • m)),
          ProjectiveSpectrum.basicOpen 𝒜 h ≤ ProjectiveSpectrum.basicOpen 𝒜 f ∧
            (AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec 𝒜 f) ⁻¹'
                  (PrimeSpectrum.basicOpen g :
                    Set (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f))) =
                Subtype.val ⁻¹' (ProjectiveSpectrum.basicOpen 𝒜 h :
                  Set (ProjectiveSpectrum 𝒜)) ∧
              g = HomogeneousLocalization.Away.mk 𝒜 f_deg n h hh)
