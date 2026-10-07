module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace Field

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- Lemma 9.14.8 (Tag 09HJ): for a finite field extension, the cardinal-valued separable degree
equals the number of base-field algebra homomorphisms into any algebraically closed target. -/
theorem sepDegree_eq_natCard_algHom_of_isAlgClosed [FiniteDimensional F K] [IsAlgClosed L] :
    sepDegree F K = Nat.card (K →ₐ[F] L) := by
  calc
    sepDegree F K = Cardinal.toNat (sepDegree F K) := by
      symm
      exact Cardinal.cast_toNat_of_lt_aleph0
        ((sepDegree_le_rank F K).trans_lt (Module.rank_lt_aleph0 F K))
    _ = finSepDegree F K := by
      simpa using
        congrArg (fun n : ℕ ↦ (n : Cardinal.{max u v})) (finSepDegree_eq F K).symm
    _ = Nat.card (K →ₐ[F] L) := by
      simpa using finSepDegree_eq_of_isAlgClosed F K L

end Field
