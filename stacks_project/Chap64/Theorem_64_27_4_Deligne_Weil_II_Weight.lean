module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Mixed and pure weights of Q_ℓ-linear endomorphisms

A `ℚ_[ℓ]`-linear endomorphism has mixed weights `≤ wmax` when its characteristic
polynomial arises by embedding a number-field polynomial, and every complex
embedding-root has absolute value `q^{w/2}` for some integer `w ≤ wmax`. Purity
is the same condition with a single weight.
-/

@[expose] public section

open Polynomial

noncomputable section

universe u

namespace Module.End

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {M : Type u} [AddCommGroup M] [Module ℚ_[ℓ] M] [FiniteDimensional ℚ_[ℓ] M]

/-- An endomorphism is mixed of weights `≤ wmax` relative to `q` when its
characteristic polynomial comes from a number field `E`, and every complex root
of every embedding `E →+* ℂ` is algebraic over `ℚ` with absolute value
`q^{w/2}` for some `w ≤ wmax`. -/
def IsMixedOfWeightsLE (f : Module.End ℚ_[ℓ] M) (q : ℕ) (wmax : ℤ) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]) (p : E[X]),
    p.map σ = LinearMap.charpoly f ∧
      ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
        IsAlgebraic ℚ α ∧ ∃ w : ℤ, w ≤ wmax ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- An endomorphism is pure of weight `w` relative to `q` when its characteristic
polynomial comes from a number field `E`, and every complex root of every
embedding `E →+* ℂ` is algebraic over `ℚ` with absolute value `q^{w/2}`. -/
def IsPureOfWeight (f : Module.End ℚ_[ℓ] M) (q : ℕ) (w : ℤ) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]) (p : E[X]),
    p.map σ = LinearMap.charpoly f ∧
      ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
        IsAlgebraic ℚ α ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- Mixed weights unpack as a number-field characteristic polynomial together with
the complex absolute-value bound `q^{w/2}` for some `w ≤ wmax`. -/
theorem isMixedOfWeightsLE_iff (f : Module.End ℚ_[ℓ] M) (q : ℕ) (wmax : ℤ) :
    f.IsMixedOfWeightsLE q wmax ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]) (p : E[X]),
        p.map σ = LinearMap.charpoly f ∧
          ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
            IsAlgebraic ℚ α ∧ ∃ w : ℤ, w ≤ wmax ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2) :=
  sorry

/-- Purity unpacks as a number-field characteristic polynomial together with the
single complex absolute value `q^{w/2}`. -/
theorem isPureOfWeight_iff (f : Module.End ℚ_[ℓ] M) (q : ℕ) (w : ℤ) :
    f.IsPureOfWeight q w ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]) (p : E[X]),
        p.map σ = LinearMap.charpoly f ∧
          ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
            IsAlgebraic ℚ α ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2) :=
  sorry

/-- Purity of weight `w` implies mixed weights `≤ w`. -/
theorem IsPureOfWeight.isMixedOfWeightsLE {f : Module.End ℚ_[ℓ] M} {q : ℕ} {w : ℤ}
    (hf : f.IsPureOfWeight q w) : f.IsMixedOfWeightsLE q w := sorry

end Module.End
