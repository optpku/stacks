module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
@stack 031B
@stack 031D
# Finite modules and quotient-finiteness over adic rings

This leaf owns the finite-module completeness criterion and the companion
finite-quotient criterion.  Under the ring-side precompleteness hypothesis, the
primary APIs use the weakest module-side formulations: finite generation plus
`IsHausdorff`, or a finite reduction modulo `I` plus `IsHausdorff`.  The
intersection formulas are retained as source-facing convenience theorems.
All declarations use Mathlib's canonical predicates, so no chapter namespace
or proof-local instance is required by downstream users.
-/

universe u v

section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace IsAdicComplete

/- The finite module and ring-side precompleteness facts are instance inputs
   because they are canonical propositions consumed by typeclass search.  The
   module-side Hausdorff fact is likewise a canonical instance for the primary
   theorem. -/
/- The intersection criterion is a separate source-facing bridge.  Its proof
   consumes the independent converse owner
   `IsHausdorff.of_iInf_pow_smul_eq_bot`; Mathlib's
   `IsHausdorff.iInf_pow_smul` has the opposite direction, so the two APIs stay
   explicitly paired rather than hiding a directional cast. -/

/-- If `R` is `I`-adically precomplete and `M` is finite and `I`-adically
Hausdorff, then `M` is `I`-adically complete. -/
@[stacks 031B "finite-module completeness from a Hausdorff hypothesis"]
theorem of_finite_of_isHausdorff
    {I : Ideal R} [IsPrecomplete I R] [Module.Finite R M] [IsHausdorff I M] :
    IsAdicComplete I M := sorry

/-- If `R` is `I`-adically precomplete and `M` is finite with vanishing
intersection of its `I`-power submodules, then `M` is `I`-adically complete. -/
@[stacks 031B "finite-module completeness from vanishing adic intersection"]
theorem of_finite_of_iInf_pow_smul_eq_bot
    {I : Ideal R} [IsPrecomplete I R] [Module.Finite R M]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsAdicComplete I M := sorry

/-- If `R` is `I`-adically complete and `M` is finite with vanishing
intersection of its `I`-power submodules, then `M` is `I`-adically complete. -/
@[stacks 031B "complete-ring source specialization"]
theorem of_finite_of_ringComplete_of_iInf_pow_smul_eq_bot
    {I : Ideal R} [IsAdicComplete I R] [Module.Finite R M]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsAdicComplete I M := sorry

end IsAdicComplete

/- The quotient-finiteness criterion belongs to the module-finiteness layer,
   even though its proof uses adic completion.  Keeping it here gives later
   callers a chapter-independent entry point alongside the source specialization. -/

/-- If `R` is `I`-adically precomplete, `M / I • ⊤` is finite over `R ⧸ I`,
and `M` is `I`-adically Hausdorff, then `M` is finite over `R`. -/
@[stacks 031D "finite generation from a finite quotient and Hausdorffness"]
theorem Module.Finite.of_quotient_of_isHausdorff
    {I : Ideal R} [IsPrecomplete I R]
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]
    [IsHausdorff I M] :
    Module.Finite R M := sorry

/-- If `R` is `I`-adically precomplete, `M / I • ⊤` is finite over `R ⧸ I`,
and the intersection of the `I`-power submodules of `M` vanishes, then `M` is
finite over `R`. -/
@[stacks 031D "finite generation from vanishing adic intersection"]
theorem Module.Finite.of_quotient_of_iInf_pow_smul_eq_bot
    {I : Ideal R} [IsPrecomplete I R]
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    Module.Finite R M := sorry

/-- If `R` is `I`-adically complete, `M / I • ⊤` is finite over `R ⧸ I`, and
the intersection of the `I`-power submodules of `M` vanishes, then `M` is
finite over `R`. -/
@[stacks 031D "complete-ring source specialization"]
theorem Module.Finite.of_quotient_of_ringComplete_of_iInf_pow_smul_eq_bot
    {I : Ideal R} [IsAdicComplete I R]
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    Module.Finite R M := sorry

end
