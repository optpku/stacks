/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# The filtered Kunneth spectral sequence

This leaf records the filtered tensor model, its first-page description, and the bounded
convergence criterion for two filtered cochain complexes of modules.

@stack 0H7Y
-/

@[expose] public section

open CategoryTheory Limits
open scoped BigOperators DerivedTensorProduct

universe u

noncomputable section

-- Local instance justification (instance diamond): the tensor model and its abutment use the
-- standard derived category of modules and its canonical quotient functor.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.FilteredComplex.Kunneth

variable {R : Type u} [CommRing R]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Proposition 15.64.3: two filtered complexes admit a filtered derived-tensor model whose
associated spectral sequence has the Kunneth first page; the four eventual stage conditions imply
boundedness, finite cohomology filtrations, and convergence. -/
@[stacks 0H7Y "filtered Kunneth spectral sequence"]
theorem exists_spectralSequence
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

end CategoryTheory.FilteredComplex.Kunneth
