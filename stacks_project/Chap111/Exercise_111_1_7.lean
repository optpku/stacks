/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Kummer.Irreducibility
import StacksCheckRecall

@[expose] public section

open Polynomial

universe u

/- Exercise 111.1.7 (1): the characteristic of a field containing a primitive
positive `n`th root of unity does not divide `n`. -/
@[stacks 02CM] #check (IsPrimitiveRoot.ringChar_not_dvd :
  ∀ {k : Type u} [Field k] {n : ℕ} {ζ : k},
    IsPrimitiveRoot ζ n → 0 < n → ¬ ringChar k ∣ n)

/- Exercise 111.1.7 (2): if `a` is not a `d`th power for any divisor `d` of `n`
with `1 < d`, the quotient adjoining a root of `X ^ n - C a` is a field. -/
@[stacks 02CM] #check (isField_adjoinRoot_X_pow_sub_C :
  ∀ {k : Type u} [Field k] {n : ℕ} {ζ : k},
    IsPrimitiveRoot ζ n → 0 < n → ∀ {a : k},
      (∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a) →
      IsField (AdjoinRoot (X ^ n - C a)))

#check (IsPrimitiveRoot.natCast_ne_zero :
  ∀ {k : Type u} [Field k] {n : ℕ} {ζ : k},
    IsPrimitiveRoot ζ n → 0 < n → (n : k) ≠ 0)

#check (X_pow_sub_C_irreducible_of_isPrimitiveRoot :
  ∀ {k : Type u} [Field k] {n : ℕ} {ζ : k},
    IsPrimitiveRoot ζ n → 0 < n → ∀ {a : k},
      (∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a) →
      Irreducible (X ^ n - C a))

#check (X_pow_sub_C_irreducible_iff_of_isPrimitiveRoot :
  ∀ {k : Type u} [Field k] {n : ℕ} {ζ : k},
    IsPrimitiveRoot ζ n → 0 < n → ∀ {a : k},
      Irreducible (X ^ n - C a) ↔ ∀ d, d ∣ n → 1 < d → ∀ b : k, b ^ d ≠ a)
