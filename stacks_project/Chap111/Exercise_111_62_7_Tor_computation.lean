/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation

@[expose] public section

noncomputable section

universe u

open MvPolynomial CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

namespace MvPolynomial

/-- Exercise 111.62.7 (Tor computation): for a field `k`, writing
`R = MvPolynomial (Fin 3) k` with `X 0`, `X 1`, `X 2` corresponding to `x`, `y`, `z`
(the source takes `k = ℂ`), `M = R ⧸ Ideal.span {X 0, X 2}` and
`N = R ⧸ Ideal.span {X 1, X 2}`, the ℕ-indexed object `Tor⁽n⁾[R](M, N)` is
nonzero if and only if `n = 0` or `n = 1`. Among `i : ℤ` the groups are therefore
nonzero precisely at `0` and `1`, since left-derived `Tor` vanishes in negative
degrees. -/
@[stacks 0FWR]
theorem tor_quotient_span_XZ_YZ_not_isZero_iff {k : Type u} [Field k] (n : ℕ) :
    ¬ IsZero
        (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) ↔
      n = 0 ∨ n = 1 :=
  sorry

/-- The degree-`0` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` is nonzero. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_zero {k : Type u} [Field k] :
    ¬ IsZero
        (Tor⁽0⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- The degree-`1` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` is nonzero. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_one {k : Type u} [Field k] :
    ¬ IsZero
        (Tor⁽1⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- For every `n ≥ 2`, the degree-`n` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` vanishes. -/
theorem tor_quotient_span_XZ_YZ_isZero_of_two_le {k : Type u} [Field k] {n : ℕ}
    (hn : 2 ≤ n) :
    IsZero
      (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
          Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
        MvPolynomial (Fin 3) k ⧸
          Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- Packaging the same vanishing set over `i : ℤ`: a nonnegative homological degree
with nonzero `Tor` exists if and only if `i = 0` or `i = 1`. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_int_iff {k : Type u} [Field k] (i : ℤ) :
    (∃ n : ℕ, i = n ∧
        ¬ IsZero
            (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
                Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
              MvPolynomial (Fin 3) k ⧸
                Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2}))) ↔
      i = 0 ∨ i = 1 :=
  sorry

end MvPolynomial
