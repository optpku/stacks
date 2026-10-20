/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Remark 111.16.2

@stack 027M
-/

universe u v

section Polynomial

variable (k : Type u) [Field k] (n : ℕ)
variable (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal]

/- Remark 111.16.2 (1): let `k` be a field. Then for every integer `n : ℕ` and every maximal
ideal `m` of `k[x_1, …, x_n]`, formalized as `MvPolynomial (Fin n) k`, the quotient
`MvPolynomial (Fin n) k ⧸ m` is a finite field extension of `k`. The preceding `ℂ` exercise
is only the special case `k = ℂ`. -/
@[stacks 027M] #check
  (Ideal.Quotient.finiteDimensional_of_finiteType k (MvPolynomial (Fin n) k) m :
    FiniteDimensional k (MvPolynomial (Fin n) k ⧸ m))

end Polynomial

section FiniteType

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]

/- Remark 111.16.2 (2): the polynomial statement implies the same conclusion for maximal ideals
of finitely generated `k`-algebras. If `A` is of finite type over a field `k` and `m` is a
maximal ideal of `A`, then `A ⧸ m` is a finite field extension of `k`. -/
@[stacks 027M] #check (Ideal.Quotient.finiteDimensional_of_finiteType k A m : FiniteDimensional k (A ⧸ m))

end FiniteType
