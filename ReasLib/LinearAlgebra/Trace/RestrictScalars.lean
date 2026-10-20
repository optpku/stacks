module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

open Module

namespace LinearMap

variable (R : Type u) {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Restricting scalars along a free tower sends the trace of an endomorphism to the algebra trace
of its original trace. -/
theorem trace_restrictScalars [AddCommMonoid A] [Module R A] [Module S A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Free S A] (f : A →ₗ[S] A) :
    trace R A (f.restrictScalars R) = Algebra.trace R S (trace S A f) := by
  classical
  by_cases hR : Subsingleton R
  · exact Subsingleton.elim _ _
  -- Local instance justification (proof-local temporary data): this nontrivial branch is required
  -- by the basis-based trace comparison.
  letI := not_subsingleton_iff_nontrivial.mp hR
  by_cases hA : Subsingleton A
  · -- Local instance justification (proof-local temporary data): the singleton module branch
    -- reduces the endomorphism and both trace expressions definitionally.
    letI := hA
    have hf : f = 0 := by ext a; exact Subsingleton.elim _ _
    subst hf
    simp
  -- Local instance justification (proof-local temporary data): the nontrivial module branch is
  -- required to select the free bases used by the matrix trace formulas.
  letI := not_subsingleton_iff_nontrivial.mp hA
  let bS := Free.chooseBasis R S
  let bA := Free.chooseBasis S A
  have := Module.nontrivial S A
  cases fintypeOrInfinite (Free.ChooseBasisIndex R S)
  · cases fintypeOrInfinite (Free.ChooseBasisIndex S A)
    · let M := toMatrix bA bA f
      rw [trace_eq_matrix_trace R (bS.smulTower' bA), restrictScalars_toMatrix,
        trace_eq_matrix_trace S bA]
      calc
        Matrix.trace ((M.map (Algebra.leftMulMatrix bS)).comp _ _ _ _ _)
            = ∑ y, Matrix.trace (Algebra.leftMulMatrix bS (M y y)) := by
                simp [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]
        _ = ∑ y, Algebra.trace R S (M y y) := by
                simp [Algebra.trace_eq_matrix_trace bS]
        _ = Algebra.trace R S (∑ y, M y y) := by
                rw [map_sum]
        _ = Algebra.trace R S (Matrix.trace M) := by
                simp [Matrix.trace]
    ·
      have hA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s S A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bA (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      simp [LinearMap.trace, hA_noBasis, hRA_noBasis]
  ·
      have hS_noBasis : ¬∃ s : Finset S, Nonempty (Basis s R S) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bS (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      rw [Algebra.trace_eq_zero_of_not_exists_basis R hS_noBasis,
        LinearMap.zero_apply]
      simp [LinearMap.trace, hRA_noBasis]

end LinearMap
