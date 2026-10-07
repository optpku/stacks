module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If the irrelevant ideal is contained in the radical of the ideal spanned by a family,
then the corresponding standard opens cover the projective spectrum. -/
theorem iSup_basicOpen_eq_top_of_irrelevant_le_radical_span {ι : Type*} (f : ι → A)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (Ideal.span (Set.range f)).radical) :
    ⨆ i, basicOpen 𝒜 (f i) = ⊤ := sorry

/-- The projective spectrum is compact exactly when finitely many homogeneous elements of
positive degree span an ideal whose radical contains the irrelevant ideal. -/
theorem isCompact_univ_iff_exists_finite_homogeneous_irrelevant_le_radical_span :
    IsCompact (Set.univ : Set (Proj 𝒜)) ↔
      ∃ n : ℕ, ∃ f : Fin n → A, ∃ deg : Fin n → ℕ,
        (∀ i, 0 < deg i ∧ f i ∈ 𝒜 (deg i)) ∧
          (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
            (Ideal.span (Set.range f)).radical := sorry

end

end AlgebraicGeometry.Proj
