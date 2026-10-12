/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.QuasiCompact
import StacksCheckRecall

@[expose] public section

universe u v

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 27.8.9: `Proj(S)` is quasi-compact if and only if finitely many homogeneous elements
of positive degree span an ideal whose radical contains the irrelevant ideal. -/
@[stacks 01MD] #check
  (AlgebraicGeometry.Proj.isCompact_univ_iff_exists_finite_homogeneous_irrelevant_le_radical_span
    𝒜 :
    IsCompact (Set.univ : Set (AlgebraicGeometry.Proj 𝒜)) ↔
      ∃ n : ℕ, ∃ f : Fin n → A, ∃ deg : Fin n → ℕ,
        (∀ i, 0 < deg i ∧ f i ∈ 𝒜 (deg i)) ∧
          (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
            (Ideal.span (Set.range f)).radical)

#check
  (AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical_span 𝒜 :
    ∀ {ι : Type*} (f : ι → A),
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
        (Ideal.span (Set.range f)).radical →
      ⨆ i, AlgebraicGeometry.Proj.basicOpen 𝒜 (f i) = ⊤)

end
