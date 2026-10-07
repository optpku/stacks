module

public import Mathlib.RingTheory.KrullDimension.Basic
public import stacks_project.Chap90.Example_90_9_6_FunctionField
public import stacks_project.Chap90.Example_90_9_6_Completion
public import stacks_project.Chap90.Lemma_90_9_5

/-!
# An explicit smooth object of `Ĉ_Λ` for a purely inseparable residue extension

For a prime `p` and `n : ℕ`, with `Λ = F_p(t_1, …, t_n)` and
`k = F_p(x_1, …, x_n)` via `t_i ↦ x_i^p`, the `I`-adic completion
`R = Λ[x_1, …, x_n]^∧_(x_i^p - t_i)` is an object of `Ĉ_Λ` as in
Lemma 90.9.5, and `n ≤ dim R`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open CompleteLocalAlgCat PurelyInseparable

noncomputable section

namespace CompleteLocalAlgCat

/-- Example 90.9.6 (1): the explicit object of `Ĉ_Λ` is the `I`-adic completion
`R = Λ[x_1, …, x_n]^∧_(x_1^p - t_1, …, x_n^p - t_n)`, for
`Λ = F_p(t_1, …, t_n)` and `k = F_p(x_1, …, x_n)` with `t_i ↦ x_i^p`. -/
@[stacks 06SN]
theorem pthPowerAdicCompletion_spec (n p : ℕ) [Fact p.Prime] :
    (pthPowerAdicCompletion n p).carrier = adicCompletion n p :=
  sorry

/-- Example 90.9.6 (2): `algebraMap Λ R` is formally smooth in the `m_R`-adic
topology. -/
@[stacks 06SN]
theorem formallySmooth_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    (algebraMap (lambdaField n p) (pthPowerAdicCompletion n p).carrier).formally_smooth_for_adic
      (maximalIdeal (pthPowerAdicCompletion n p).carrier) :=
  sorry

/-- Restricted coyoneda of `pthPowerAdicCompletion` is smooth, by Lemma 90.9.3. -/
instance instIsSmooth_restrictedCoyoneda_pthPowerAdicCompletion
    (n p : ℕ) [Fact p.Prime] :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda (pthPowerAdicCompletion n p))) :=
  sorry

/-- Example 90.9.6 (3): the canonical map `H1Cotangent Λ k → m_R / m_R²` is bijective. -/
@[stacks 06SN]
theorem bijective_toKerCotangent_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (toKerCotangent (lambdaField n p) (pthPowerAdicCompletion n p).carrier
        (functionField n p) (algebraMap_surjective (pthPowerAdicCompletion n p))) :=
  sorry

/-- Example 90.9.6 (4): the base-change map `Ω[R⁄Λ] ⊗[R] k → Ω[k⁄Λ]` is bijective. -/
@[stacks 06SN]
theorem bijective_mapBaseChange_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (mapBaseChange (lambdaField n p) (pthPowerAdicCompletion n p).carrier
        (functionField n p)) :=
  sorry

/-- Example 90.9.6 (5): one cannot do better in this example, in the sense that
`n ≤ dim R`. -/
@[stacks 06SN]
theorem le_ringKrullDim_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    (n : WithBot ℕ∞) ≤ ringKrullDim (pthPowerAdicCompletion n p).carrier :=
  sorry

end CompleteLocalAlgCat
