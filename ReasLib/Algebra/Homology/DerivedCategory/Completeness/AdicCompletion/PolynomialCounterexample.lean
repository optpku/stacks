module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# A derived-complete module that is not adically complete

For a prime `p`, substitution `X ↦ p * X` on `ℤ_[p][X]` extends to its ordinary `p`-adic
completion.  The cokernel is derived complete, but the explicit geometric-series class shows that
it is not ordinarily complete.

@stack 0G3F
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open scoped BigOperators

namespace PadicPolynomialCompletion

variable (p : ℕ) [Fact p.Prime]

local notation "Zp" => ℤ_[p]
local notation "ZpPoly" => Polynomial Zp
local notation "I" => principalIdeal (p : Zp)
local notation "ZpPolyHat" => AdicCompletion I ZpPoly

/-- The map on `p`-adic completions induced by polynomial substitution `X ↦ p * X`. -/
@[stacks 0G3F "completed polynomial substitution"]
abbrev substitution : ZpPolyHat →ₗ[Zp] ZpPolyHat :=
  (AdicCompletion.map I
    ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap)).restrictScalars Zp

/-- Example 15.94.4 (1) (Stacks `0G3F`): the counterexample module is the cokernel of the
completed substitution `X ↦ p * X`. -/
@[stacks 0G3F "(1), completed-substitution cokernel"]
abbrev substitutionCokernel : ModuleCat Zp :=
  cokernel (ModuleCat.ofHom (substitution p))

/-- Example 15.94.4 (2) (Stacks `0G3F`): the completed-substitution cokernel is derived complete
with respect to `(p)`. -/
@[stacks 0G3F "(2), derived completeness"]
theorem substitutionCokernel_isDerivedComplete :
    (substitutionCokernel p).IsDerivedCompleteWithRespectTo I := sorry

/-- The `n`th polynomial truncation of `1 + p * X + p ^ 2 * X ^ 2 + ⋯`. -/
@[stacks 0G3F "geometric-series polynomial truncation"]
abbrev geometricTruncation (n : ℕ) : ZpPoly :=
  ∑ i ∈ Finset.range n, C ((p : Zp) ^ i) * X ^ i

/-- The linear map to the `n`th adic quotient determined by the truncated geometric series. -/
@[stacks 0G3F "geometric-series adic quotient map"]
abbrev geometricToQuotient (n : ℕ) :
    Zp →ₗ[Zp] (ZpPoly ⧸ ((I ^ n) • (⊤ : Submodule Zp ZpPoly))) :=
  (Submodule.mkQ ((I ^ n) • (⊤ : Submodule Zp ZpPoly))).comp <|
    LinearMap.smulRight (LinearMap.id : Zp →ₗ[Zp] Zp) (geometricTruncation p n)

/-- The truncated geometric-series maps are compatible with all adic quotient transitions. -/
theorem geometricToQuotient_compatible {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I ZpPoly hmn ∘ₗ geometricToQuotient p n =
      geometricToQuotient p m := sorry

/-- Example 15.94.4 (3) (Stacks `0G3F`): the completion element represented by the compatible
truncations `∑ i < n, p ^ i * X ^ i`. -/
@[stacks 0G3F "(3), geometric-series completion element"]
noncomputable abbrev geometricSeries : ZpPolyHat :=
  (AdicCompletion.lift I (geometricToQuotient p)
    fun hmn ↦ geometricToQuotient_compatible p hmn) 1

/-- Evaluation of the geometric-series completion element is its displayed truncation. -/
theorem geometricSeries_eval (n : ℕ) :
    AdicCompletion.eval I ZpPoly n (geometricSeries p) =
      Submodule.mkQ ((I ^ n) • (⊤ : Submodule Zp ZpPoly)) (geometricTruncation p n) := sorry

/-- The class of the explicit geometric series in the completed-substitution cokernel. -/
@[stacks 0G3F "geometric-series cokernel class"]
noncomputable abbrev geometricClass : substitutionCokernel p :=
  (cokernel.π (ModuleCat.ofHom (substitution p))).hom (geometricSeries p)

/-- Example 15.94.4 (4) (Stacks `0G3F`): the geometric-series class in the cokernel is nonzero. -/
@[stacks 0G3F "(4), nonzero geometric-series class"]
theorem geometricClass_ne_zero : geometricClass p ≠ 0 := sorry

/-- Example 15.94.4 (5) (Stacks `0G3F`): the geometric-series class belongs to every
`p ^ n`-multiple submodule of the cokernel. -/
@[stacks 0G3F "(5), geometric-series class in every power"]
theorem geometricClass_mem_pow (n : ℕ) :
    geometricClass p ∈ (I ^ n) • (⊤ : Submodule Zp (substitutionCokernel p)) := sorry

/-- Example 15.94.4 (6) (Stacks `0G3F`): the derived-complete cokernel is not ordinarily
`(p)`-adically complete. -/
@[stacks 0G3F "(6), failure of ordinary adic completeness"]
theorem substitutionCokernel_not_isAdicComplete :
    ¬ IsAdicComplete I (substitutionCokernel p) := sorry

end PadicPolynomialCompletion
