/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.RingTheory.RingHom.PowerImage.Surjective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Positive powers in field extensions

@stack 0BR7

This leaf owns the field-level alternative behind the positive-power-in-the-image criterion.
The exceptional branch is expressed as algebraicity over a prime field, independently of any
numbered chapter or of a particular proof via roots of unity.
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- A field is algebraic over a fixed `ZMod p` once a characteristic witness is supplied.  The
canonical algebra is an explicit argument here, so callers do not have to reproduce a local
`Algebra` instance merely to state algebraicity. -/
def IsAlgebraicOverZMod
    (K : Type u) [Field K] (p : ℕ) (hchar : CharP K p) : Prop :=
  @Algebra.IsAlgebraic (ZMod p) K _ _ (@ZMod.algebra K _ p hchar)

/-- A field is algebraic over one of its prime fields.  The prime and characteristic witnesses
are explicit data; the corresponding `ZMod p` algebra is owned by `IsAlgebraicOverZMod`. -/
@[stacks 0BR7 "prime-field algebraic branch"]
def IsPrimeAlgebraic (K : Type u) [Field K] : Prop :=
  ∃ p : ℕ, ∃ hp : p.Prime, ∃ hchar : CharP K p,
    IsAlgebraicOverZMod K p hchar

/-- A prime and a characteristic-`p` algebraicity witness construct the prime-field branch. -/
@[stacks 0BR7 "prime-field algebraic constructor"]
theorem isPrimeAlgebraic_of
    {K : Type u} [Field K] (p : ℕ) (hp : p.Prime)
    (hchar : CharP K p) (hAlg : IsAlgebraicOverZMod K p hchar) :
    IsPrimeAlgebraic K := sorry

/-- For a field extension, power-surjectivity is equivalent to surjectivity, a positive-characteristic
purely inseparable extension, or algebraicity over a prime field. -/
@[stacks 0BR7]
theorem iff_isPowerSurjective
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] :
    RingHom.IsPowerSurjective (algebraMap k K) ↔
      Function.Surjective (algebraMap k K) ∨
        (ringChar k ≠ 0 ∧ IsPurelyInseparable k K) ∨ IsPrimeAlgebraic K := sorry

/-- Every target element has a positive power in the source image exactly in the surjective,
positive-characteristic purely inseparable, or prime-field-algebraic cases. -/
@[stacks 0BR7]
theorem iff_forall_pow_mem_range
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] :
    (∀ x : K, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap k K).range) ↔
      Function.Surjective (algebraMap k K) ∨
        (ringChar k ≠ 0 ∧ IsPurelyInseparable k K) ∨ IsPrimeAlgebraic K := sorry

end FieldExtension
