/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

open Polynomial

universe u

variable {k : Type u} [Field k]

/-- A positive natural number with a primitive root of unity in a field has
nonzero natural cast in that field. -/
theorem IsPrimitiveRoot.natCast_ne_zero {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) : (n : k) ≠ 0 := sorry

/-- The characteristic of a field does not divide a positive natural number
whose primitive root of unity lies in the field. -/
theorem IsPrimitiveRoot.ringChar_not_dvd {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) : ¬ ringChar k ∣ n := sorry

/-- In a field containing a primitive `n`th root of unity with `0 < n`, the
polynomial `X ^ n - C a` is irreducible if `a` is not a `d`th power for any
divisor `d` of `n` with `1 < d`. -/
theorem X_pow_sub_C_irreducible_of_isPrimitiveRoot {n : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) {a : k}
    (ha : ∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a) :
    Irreducible (X ^ n - C a) := sorry

/-- In a field containing a primitive `n`th root of unity with `0 < n`,
irreducibility of `X ^ n - C a` is equivalent to `a` not being a `d`th power
for any divisor `d` of `n` with `1 < d`. -/
theorem X_pow_sub_C_irreducible_iff_of_isPrimitiveRoot {n : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) {a : k} :
    Irreducible (X ^ n - C a) ↔ ∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a := sorry

/-- In a field containing a primitive `n`th root of unity with `0 < n`, the
quotient adjoining a root of `X ^ n - C a` is a field if `a` is not a `d`th
power for any divisor `d` of `n` with `1 < d`. -/
theorem isField_adjoinRoot_X_pow_sub_C {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) {a : k} (ha : ∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a) :
    IsField (AdjoinRoot (X ^ n - C a)) := sorry
