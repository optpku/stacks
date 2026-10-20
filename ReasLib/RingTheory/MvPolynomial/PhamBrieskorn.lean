/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Pham–Brieskorn hypersurface rings

The coordinate ring `k[x, y, z] ⧸ (x ^ r + y ^ s + z ^ t)` and its coordinates.
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial

namespace MvPolynomial.PhamBrieskorn

/-- The Pham–Brieskorn polynomial `X 0 ^ r + X 1 ^ s + X 2 ^ t`. -/
def relation (k : Type u) [CommRing k] (r s t : ℕ) : MvPolynomial (Fin 3) k :=
  X 0 ^ r + X 1 ^ s + X 2 ^ t

/-- The Pham–Brieskorn hypersurface ring `k[x, y, z] ⧸ (x ^ r + y ^ s + z ^ t)`. -/
abbrev Ring (k : Type u) [CommRing k] (r s t : ℕ) :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {relation k r s t}

/-- The class of `x` in the Pham–Brieskorn ring. -/
def x (k : Type u) [CommRing k] (r s t : ℕ) : Ring k r s t :=
  Ideal.Quotient.mk _ (X 0)

/-- The class of `y` in the Pham–Brieskorn ring. -/
def y (k : Type u) [CommRing k] (r s t : ℕ) : Ring k r s t :=
  Ideal.Quotient.mk _ (X 1)

/-- The class of `z` in the Pham–Brieskorn ring. -/
def z (k : Type u) [CommRing k] (r s t : ℕ) : Ring k r s t :=
  Ideal.Quotient.mk _ (X 2)

/-- The Pham–Brieskorn relation vanishes in the quotient. -/
theorem mk_relation (k : Type u) [CommRing k] (r s t : ℕ) :
    Ideal.Quotient.mk (Ideal.span {relation k r s t}) (relation k r s t) = 0 :=
  sorry

/-- The coordinate equation `x ^ r + y ^ s + z ^ t = 0` in the Pham–Brieskorn ring. -/
theorem x_pow_add_y_pow_add_z_pow (k : Type u) [CommRing k] (r s t : ℕ) :
    x k r s t ^ r + y k r s t ^ s + z k r s t ^ t = 0 :=
  sorry

/-- The Pham–Brieskorn polynomial is irreducible for pairwise coprime exponents. -/
theorem irreducible_relation (k : Type u) [Field k] (r s t : ℕ)
    (hrs : Nat.Coprime r s) (hrt : Nat.Coprime r t) (hst : Nat.Coprime s t) :
    Irreducible (relation k r s t) :=
  sorry

/-- The Pham–Brieskorn ring is a domain for pairwise coprime exponents. -/
instance instIsDomain (k : Type u) [Field k] (r s t : ℕ)
    [Fact (Nat.Coprime r s)] [Fact (Nat.Coprime r t)] [Fact (Nat.Coprime s t)] :
    IsDomain (Ring k r s t) :=
  sorry

/-- The class of `z` is prime in the Pham–Brieskorn ring. -/
theorem prime_z (k : Type u) [Field k] (r s t : ℕ)
    (hrs : Nat.Coprime r s) (hrt : Nat.Coprime r t) (hst : Nat.Coprime s t) :
    Prime (z k r s t) :=
  sorry

end MvPolynomial.PhamBrieskorn
