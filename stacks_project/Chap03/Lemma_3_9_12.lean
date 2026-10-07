module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.12: an fppf covering `{f i : Xi i ⟶ X}` of a scheme `X` admits an fppf covering
`{g j : W j ⟶ X}` which refines it, with `(∐ W).size ≤ X.size`. -/
@[stacks 0AHL]
theorem exists_fppfCovering_refinement_size_le {X : Scheme.{u}} {ι : Type v}
    (Xi : ι → Scheme.{u}) (f : (i : ι) → Xi i ⟶ X)
    (hf : Presieve.ofArrows Xi f ∈ fppfPrecoverage X) :
    ∃ (J : Type u) (W : J → Scheme.{u}) (g : (j : J) → W j ⟶ X)
      (hg : Presieve.ofArrows W g ∈ fppfPrecoverage X) (s : J → ι)
      (h : (j : J) → W j ⟶ Xi (s j)),
      (∀ j, h j ≫ f (s j) = g j) ∧ (∐ W).size ≤ X.size := sorry

/-- There exists an fppf cover of `X` in universe `u` which refines `𝒰` and whose coproduct has
size at most `X.size`. -/
theorem exists_fppfCover_refinement_size_le {X : Scheme.{u}}
    (𝒰 : X.Cover.{v} fppfPrecoverage) :
    ∃ (𝒱 : X.Cover.{u} fppfPrecoverage)
      (φ : Precoverage.ZeroHypercover.Hom fppfPrecoverage 𝒱 𝒰),
      (∐ 𝒱.X).size ≤ X.size := sorry

end AlgebraicGeometry.Scheme
