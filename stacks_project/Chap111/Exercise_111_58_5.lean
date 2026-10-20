/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Laurent
import StacksCheckRecall

@[expose] public section

universe u

open scoped LaurentPolynomial Polynomial
open LaurentPolynomial

/- Exercise 111.58.5: if `k` is a field, writing `A = k[T;T⁻¹]` and `B = k[X]`, every
`k`-algebra map `φ : A →ₐ[k] B` sends the Laurent generator `T 1` (the source variable `x`)
to a constant polynomial. -/
@[stacks 0D5K] #check (LaurentPolynomial.map_T_eq_C :
  ∀ {k : Type u} [Field k] (φ : k[T;T⁻¹] →ₐ[k] k[X]),
    ∃ c : k, φ (T 1) = Polynomial.C c)
