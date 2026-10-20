/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import StacksCheckRecall

/-!
# Unique factorization in polynomial rings

@stack 0BC1
-/

@[expose] public section

universe u

section Polynomial

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.10 (1): Stacks `0BC1` first states that a polynomial ring over a UFD is a
UFD. -/
@[stacks 0BC1 "(1)"]
#check (Polynomial.uniqueFactorizationMonoid :
  UniqueFactorizationMonoid (Polynomial R))

end Polynomial

section MvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/- Lemma 10.120.10 (2): the finite-variable polynomial ring over a field is the corresponding
multivariable specialization. -/
@[stacks 0BC1 "(2)"]
#check (MvPolynomial.uniqueFactorizationMonoid (Fin n) :
  UniqueFactorizationMonoid (MvPolynomial (Fin n) k))

end MvPolynomial
