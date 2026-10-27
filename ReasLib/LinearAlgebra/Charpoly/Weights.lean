/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Mixed and pure weights of linear endomorphisms

A linear endomorphism over a field has mixed weights `≤ wmax` when its characteristic
polynomial arises by embedding a number-field polynomial, and every complex
embedding-root has absolute value `q^{w/2}` for some integer `w ≤ wmax`. Purity
is the same condition with a single weight.
-/

@[expose] public section

open Polynomial

noncomputable section

universe u v

namespace Module.End

variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- An endomorphism is mixed of weights `≤ wmax` relative to `q` when its
characteristic polynomial comes from a number field `E`, and every complex root
of every embedding `E →+* ℂ` is algebraic over `ℚ` with absolute value
`q^{w/2}` for some `w ≤ wmax`. -/
def IsMixedOfWeightsLE (f : Module.End K M) (q : ℕ) (wmax : ℤ) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* K) (p : E[X]),
    p.map σ = LinearMap.charpoly f ∧
      ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
        IsAlgebraic ℚ α ∧ ∃ w : ℤ, w ≤ wmax ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- An endomorphism is pure of weight `w` relative to `q` when its characteristic
polynomial comes from a number field `E`, and every complex root of every
embedding `E →+* ℂ` is algebraic over `ℚ` with absolute value `q^{w/2}`. -/
def IsPureOfWeight (f : Module.End K M) (q : ℕ) (w : ℤ) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* K) (p : E[X]),
    p.map σ = LinearMap.charpoly f ∧
      ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
        IsAlgebraic ℚ α ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- Mixed weights unpack as a number-field characteristic polynomial together with
the complex absolute-value bound `q^{w/2}` for some `w ≤ wmax`. -/
theorem isMixedOfWeightsLE_iff (f : Module.End K M) (q : ℕ) (wmax : ℤ) :
    f.IsMixedOfWeightsLE q wmax ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* K) (p : E[X]),
        p.map σ = LinearMap.charpoly f ∧
          ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
            IsAlgebraic ℚ α ∧ ∃ w : ℤ, w ≤ wmax ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2) :=
  sorry

/-- Purity unpacks as a number-field characteristic polynomial together with the
single complex absolute value `q^{w/2}`. -/
theorem isPureOfWeight_iff (f : Module.End K M) (q : ℕ) (w : ℤ) :
    f.IsPureOfWeight q w ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* K) (p : E[X]),
        p.map σ = LinearMap.charpoly f ∧
          ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α →
            IsAlgebraic ℚ α ∧ ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2) :=
  sorry

/-- Purity of weight `w` implies mixed weights `≤ w`. -/
theorem IsPureOfWeight.isMixedOfWeightsLE {f : Module.End K M} {q : ℕ} {w : ℤ}
    (hf : f.IsPureOfWeight q w) : f.IsMixedOfWeightsLE q w := sorry

end Module.End
