module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace Module

/-- Remark 64.20.3. Stacks develops traces more than determinants, so the finite-coefficient
identity of Theorem 64.20.1 is harder than the `ℚ_[ℓ]` identity of Theorem 64.20.2; only
the latter is proved here, and the former is cited from SGA 4.5. There is no more general
`ℤ_[ℓ]`-coefficient form of this cohomological L-identity: `LinearMap.eulerFactor` /
`det(1 - f T)` needs a finite projective module, which over `ℤ_[ℓ]` forces `IsTorsionFree`. -/
@[stacks 03V1]
theorem not_projective_of_not_isTorsionFree {ℓ : ℕ} [Fact ℓ.Prime] {M : Type u}
    [AddCommGroup M] [Module ℤ_[ℓ] M] (hM : ¬ IsTorsionFree ℤ_[ℓ] M) :
    ¬ Projective ℤ_[ℓ] M := sorry

/-- Projective `ℤ_[ℓ]`-modules are torsion-free, which is the positive form of the
obstruction to a general determinant identity in `PowerSeries ℤ_[ℓ]`. -/
instance instIsTorsionFree_of_projective {ℓ : ℕ} [Fact ℓ.Prime] {M : Type u}
    [AddCommGroup M] [Module ℤ_[ℓ] M] [Projective ℤ_[ℓ] M] :
    IsTorsionFree ℤ_[ℓ] M := sorry

/-- The cyclic module `ℤ_[ℓ] ⧸ Ideal.span {ℓ}` is not torsion-free, hence is not projective. -/
theorem not_projective_span_prime {ℓ : ℕ} [Fact ℓ.Prime] :
    ¬ Projective ℤ_[ℓ] (ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ])}) := sorry

end Module
