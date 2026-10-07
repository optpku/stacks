module

public import stacks_project.Chap99.Lemma_99_11_3
public import stacks_project.Chap99.Lemma_99_11_7_WithSection

/-!
# Split exactness of `0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T) → 0`

If `σ : B ⟶ X` is a section of `f` and `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an
isomorphism for every scheme `T` over `B`, the Picard sequence of Lemma 99.11.3
is split exact, with splitting `σ_T^*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.4 (1): in Situation 99.11.1, if `σ : B ⟶ X` is a section of `f`
and `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`,
then `picardPullback (fiberToBase f τ) : Pic(T) → Pic(X_T)` is injective. -/
@[stacks 0D28]
theorem picardSequence_injective (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (h_iso : ∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ)))
    (τ : SchemesOver B) :
    Function.Injective (picardPullback (fiberToBase f τ)) :=
  sorry

/-- Lemma 99.11.4 (2): in Situation 99.11.1, under the same hypotheses, the
sequence is exact at `Pic(X_T)`: `toFunctor f τ L = toFunctor f τ 0` if and
only if `L` lies in the range of `picardPullback (fiberToBase f τ)`. -/
@[stacks 0D28]
theorem picardSequence_exactAt (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (h_iso : ∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ)))
    (τ : SchemesOver B) (L : (fiber f τ).PicardGroup) :
    toFunctor f τ L = toFunctor f τ 0 ↔
      L ∈ Set.range (picardPullback (fiberToBase f τ)) :=
  sorry

/-- Lemma 99.11.4 (3): in Situation 99.11.1, under the same hypotheses,
`toFunctor f τ : Pic(X_T) → Pic_{X/B}(T)` is surjective. -/
@[stacks 0D28]
theorem picardSequence_surjective (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (h_iso : ∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ)))
    (τ : SchemesOver B) :
    Function.Surjective (toFunctor f τ) :=
  sorry

/-- Lemma 99.11.4 (4): in Situation 99.11.1, under the same hypotheses,
`Picard.WithSection.sectionPicard f σ hσ τ` is a left inverse of
`picardPullback (fiberToBase f τ)`, i.e. `σ_T^* ∘ f_T^* = id` on `Pic(T)`. -/
@[stacks 0D28]
theorem picardSequence_split (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (h_iso : ∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ)))
    (τ : SchemesOver B) :
    Function.LeftInverse (Picard.WithSection.sectionPicard f σ hσ τ)
      (picardPullback (fiberToBase f τ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
