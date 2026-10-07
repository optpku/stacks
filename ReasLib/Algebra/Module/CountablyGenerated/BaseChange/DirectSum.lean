module

public import Mathlib.Algebra.DirectSum.Decomposition
public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange.Submodule
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countable scalar-extension closure along an internal direct sum

The data-facing API uses Mathlib's canonical `DirectSum.Decomposition`. A proposition-facing
bridge accepts `DirectSum.IsInternal`, while the source-facing theorem records the equivalent
`iSupIndep` and spanning conditions.
-/

universe u v w x

open scoped TensorProduct

namespace DirectSum.Decomposition

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {I : Type x}

/-- A countably generated submodule of an internal direct sum is supported on a countable
subfamily of summands. -/
@[stacks 05A8 "countable subfamily support"]
theorem exists_countable_subfamily_le (Q : I → Submodule R M)
    [DecidableEq I] [DirectSum.Decomposition Q] {P : Submodule R M}
    (hP : P.CountablyGenerated) :
    ∃ J : Set I, J.Countable ∧ P ≤ ⨆ i : J, Q i.1 := sorry

end DirectSum.Decomposition

namespace DirectSum.IsInternal

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {I : Type x}

/-- Proposition-facing form of `DirectSum.Decomposition.exists_countable_subfamily_le`. -/
@[stacks 05A8 "countable subfamily support"]
theorem exists_countable_subfamily_le {Q : I → Submodule R M}
    [DecidableEq I] (hQ : DirectSum.IsInternal Q) {P : Submodule R M}
    (hP : P.CountablyGenerated) :
    ∃ J : Set I, J.Countable ∧ P ≤ ⨆ i : J, Q i.1 := sorry

end DirectSum.IsInternal

namespace Submodule.CountablyGenerated.BaseChange

section Semiring

variable {R : Type u} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {I : Type x}

/-- Given explicit decomposition data, the base change of a countably generated enlargement can
be chosen to be exactly a countable subfamily of the summands. -/
@[stacks 05A8 "decomposition-data form"]
theorem exists_supermodule_eq_iSup_of_decomposition
    (Q : I → Submodule S (S ⊗[R] M))
    [DecidableEq I] [DirectSum.Decomposition Q]
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M} (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (J : Set I),
      N ≤ N' ∧ N'.CountablyGenerated ∧ J.Countable ∧
        N'.baseChange S = ⨆ i : J, Q i.1 := sorry

/-- Given an internal direct sum, the base change of a countably generated enlargement can be
chosen to be exactly a countable subfamily of the summands. -/
@[stacks 05A8 "internal-direct-sum form"]
theorem exists_supermodule_eq_iSup_of_isInternal
    (Q : I → Submodule S (S ⊗[R] M)) [DecidableEq I]
    (hInternal : DirectSum.IsInternal Q)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M} (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (J : Set I),
      N ≤ N' ∧ N'.CountablyGenerated ∧ J.Countable ∧
        N'.baseChange S = ⨆ i : J, Q i.1 := sorry

/-- Semiring form of the countable enlargement theorem for an internal direct sum after scalar
extension. -/
@[stacks 05A8 "semiring form"]
theorem exists_supermodule_eq_iSup (Q : I → Submodule S (S ⊗[R] M))
    (hIndependent : iSupIndep Q) (hSpans : (⨆ i, Q i) = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M} (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (J : Set I),
      N ≤ N' ∧ N'.CountablyGenerated ∧
        N'.baseChange S = ⨆ i : J, Q i.1 := sorry

end Semiring

end Submodule.CountablyGenerated.BaseChange
