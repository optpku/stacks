/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded-commutative direct-sum algebras

This leaf owns the Koszul commutativity conditions for a nonnegatively graded algebra presented
by its homogeneous pieces.  The ordinary graded semiring and algebra operations remain owned by
`DirectSum.GSemiring` and `DirectSum.GAlgebra`.
-/

@[expose] public section

universe u v

namespace DirectSum.Graded

variable (R : Type u) [CommRing R]
variable (A : ℕ → Type v)
variable [∀ n, AddCommMonoid (A n)] [∀ n, Module R (A n)]
variable [DirectSum.GSemiring A]

/-- A nonnegatively graded algebra is graded commutative when swapping homogeneous factors of
degrees `p` and `q` introduces the Koszul sign `(-1) ^ (p * q)`. -/
class IsCommutative [DirectSum.GAlgebra R A] : Prop where
  /-- Swapping homogeneous factors introduces the Koszul sign. -/
  mul_comm (p q : ℕ) (x : A p) (y : A q) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg A (Nat.add_comm q p))
        (((-1 : R) ^ (p * q)) • GradedMonoid.GMul.mul y x)

variable [DirectSum.GAlgebra R A]

/-- Homogeneous multiplication in a graded-commutative direct-sum algebra obeys the Koszul sign
rule. -/
theorem mul_comm_apply [h : IsCommutative R A]
    (p q : ℕ) (x : A p) (y : A q) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg A (Nat.add_comm q p))
        (((-1 : R) ^ (p * q)) • GradedMonoid.GMul.mul y x) := sorry

/-- A graded algebra is strictly graded commutative when it is graded commutative and every
odd-degree homogeneous element has square zero. -/
class IsStrictlyCommutative : Prop extends IsCommutative R A where
  /-- Odd-degree homogeneous elements square to zero. -/
  sq_eq_zero_of_odd {p : ℕ} (hp : Odd p) (x : A p) :
    GradedMonoid.GMul.mul x x = 0

/-- Odd homogeneous elements square to zero in a strictly graded-commutative direct-sum
algebra. -/
theorem mul_self_eq_zero_of_odd [h : IsStrictlyCommutative R A]
    {p : ℕ} (hp : Odd p) (x : A p) :
    GradedMonoid.GMul.mul x x = 0 := sorry

end DirectSum.Graded
