module

public import stacks_project.Chap62.Lemma_62_7_4_Equidimensional

/-!
# Lemma 62.7.4

Equidimensionality of a relative `r`-cycle may be checked Zariski locally on
the source and target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.7.4: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r ≥ 0` be an integer. Let `α`
be a relative `r`-cycle on `X / S`. Then to check that `α` is equidimensional
we may work Zariski locally on `X` and `S`. -/
@[stacks 0H5L]
theorem isEquidimensional_iff_of_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {ι κ : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (V : κ → S.Opens) (hV : iSup V = ⊤) :
    Equidimensional α ↔
      ∀ i j, Equidimensional
        (restrict α (U i ⊓ f ⁻¹ᵁ V j) (V j) inf_le_right) := sorry

end AlgebraicGeometry.RelativeCycle
