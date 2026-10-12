/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence

@[expose] public section

/-!
# The filtered Künneth spectral sequence

@stack 0H7Y
-/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators DerivedTensorProduct

noncomputable section

universe u

-- Local instance justification (instance diamond): fix the standard derived-category model only
-- while stating the canonical filtered tensor comparison.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Kunneth.Filtered

variable {R : Type u} [CommRing R]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Proposition 15.64.3, tag `0H7Y`: two filtered complexes admit a filtered
tensor model and its first-page spectral sequence; the four eventual stage
conditions imply boundedness, finite cohomology filtrations, and convergence. -/
@[stacks 0H7Y]
theorem existsSpectralSequence
    (K L : FilteredCochainComplex (ModuleCat R)) :
    ∃ (T : FilteredCochainComplex (ModuleCat R))
      (representationIso :
        DerivedCategory.Q.obj T.underlying ≅
          (DerivedCategory.Q.obj K.underlying ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (E : CohomologicalSpectralSequence (ModuleCat R) 0)
      (associated : T.IsAssociated E)
      (abutmentIso : ∀ n : ℤ,
        T.underlying.homology n ≅
          (H n).obj (DerivedCategory.Q.obj K.underlying ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              (DerivedCategory.Q.obj (K.gradedPiece i) ⊗[R]^L
                DerivedCategory.Q.obj (L.gradedPiece (p - i)))),
      (∃ pK₀ : ℤ, ∀ ⦃p : ℤ⦄, pK₀ ≤ p → (K.stage p).Acyclic) →
        (∃ pK₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ pK₁ → QuasiIso (K.stageInclusion p)) →
          (∃ pL₀ : ℤ, ∀ ⦃p : ℤ⦄, pL₀ ≤ p → (L.stage p).Acyclic) →
            (∃ pL₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ pL₁ → QuasiIso (L.stageInclusion p)) →
              E.IsBounded ∧
                FilteredComplex.Cohomology.Filtration.IsFinite T ∧
                  FilteredComplex.Cohomology.Convergence.Converges T E := sorry

end CategoryTheory.Kunneth.Filtered
