module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_28_2_RestrictedPowerSeries

@[expose] public section

universe u v

open IAdicRestrictedPowerSeries

namespace IAdicRestrictedPowerSeries

variable {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A)

/-- Remark 87.28.2 (1): if `A` is `I`-adically complete, then the `I`-adic completion
`A[σ]^∧` of `A[σ]` is the restricted power series ring `A{σ}` as a ring. -/
@[stacks 0AL0]
theorem compatibleStages_liftUnique [IsAdicComplete I A]
    (f : (n : ℕ) → MvPolynomial σ (A ⧸ I ^ n)) (hf : CompatibleStages σ I f) :
    ∃! F : IAdicRestrictedPowerSeries σ I, ∀ n, stageHom σ I n F = f n :=
  sorry

/-- Remark 87.28.2 (2): the limit topology on `A{σ}` is always complete, whereas the
`I`-adic topology on `A[σ]^∧` need not be. -/
@[stacks 0AL0]
theorem completeSpace_limitUniformSpace [IsAdicComplete I A] :
    @CompleteSpace (IAdicRestrictedPowerSeries σ I) (limitUniformSpace σ I) :=
  sorry

/-- Remark 87.28.2 (3): if `I` is finitely generated, then `A{σ}` and `A[σ]^∧` agree as
topological rings, by Algebra, Lemma 10.96.3. -/
@[stacks 0AL0]
theorem limitTopology_eq_adic [IsAdicComplete I A] (hI : I.FG) :
    limitTopology σ I = (extendedIdeal σ I).adicTopology :=
  sorry

/-- If `I` is finitely generated, the `I`-adic completion of `A[σ]` is itself adically complete. -/
theorem isAdicComplete_of_fg (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap A (MvPolynomial σ A))) (IAdicRestrictedPowerSeries σ I) :=
  sorry

end IAdicRestrictedPowerSeries
