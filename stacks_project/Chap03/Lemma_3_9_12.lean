/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Size
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/- Lemma 3.9.12: an fppf covering `{f i : Xi i ⟶ X}` of a scheme `X` admits an fppf covering
`{g j : W j ⟶ X}` which refines it, with `(∐ W).size ≤ X.size`. -/
@[stacks 0AHL] #check
  (AlgebraicGeometry.Scheme.exists_fppfCovering_refinement_size_le :
    ∀ {X : Scheme.{u}} {ι : Type v}
      (Xi : ι → Scheme.{u}) (f : (i : ι) → Xi i ⟶ X)
      (hf : Presieve.ofArrows Xi f ∈ fppfPrecoverage X),
      ∃ (J : Type u) (W : J → Scheme.{u}) (g : (j : J) → W j ⟶ X)
        (hg : Presieve.ofArrows W g ∈ fppfPrecoverage X) (s : J → ι)
        (h : (j : J) → W j ⟶ Xi (s j)),
        (∀ j, h j ≫ f (s j) = g j) ∧ (∐ W).size ≤ X.size)

#check (AlgebraicGeometry.Scheme.exists_fppfCover_refinement_size_le :
  ∀ {X : Scheme.{u}} (𝒰 : X.Cover.{v} fppfPrecoverage),
    ∃ (𝒱 : X.Cover.{u} fppfPrecoverage)
      (φ : Precoverage.ZeroHypercover.Hom fppfPrecoverage 𝒱 𝒰),
      (∐ 𝒱.X).size ≤ X.size)

end AlgebraicGeometry.Scheme
