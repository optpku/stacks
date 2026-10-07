module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.Ideal

@[expose] public section

/-!
# Prime fibers of finite invariant extensions

This leaf records the fixed-point consequence of the transitive prime-fiber theorem: a stable
prime is the unique prime in the fiber over its canonical contraction.  The statement is
independent of fields, integral closures, and a chosen presentation of the acting group.
@stack 0BU6
-/

universe u v w

open scoped Pointwise

namespace Algebra.IsInvariant

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [Algebra.IsInvariant A B G]

/-- A stable prime is the unique prime of `B` lying over its canonical contraction to `A`. -/
@[stacks 0BU6 "finite invariant prime fiber uniqueness"]
theorem eq_of_mem_primesOver_under_of_isStable
    (P : Ideal B) [P.IsPrime] (hP : P.IsStable G)
    (Q : (P.under A).primesOver B) : Q.1 = P := sorry

-- Proof strategy: use transitivity of the finite invariant action on primes with the same
-- contraction to obtain `g : G` carrying `P` to `Q`; stability gives `g • P = P`, so the chosen
-- prime in the fiber equals `P`.

/-- The prime fiber over the canonical contraction of a stable prime is the corresponding
singleton. -/
@[stacks 0BU6 "finite invariant prime fiber singleton"]
theorem primesOver_under_eq_singleton_of_isStable
    (P : Ideal B) [P.IsPrime] (hP : P.IsStable G) :
    (P.under A).primesOver B = {P} := sorry

-- Proof strategy: extensionality on ideals in the prime fiber.  The forward implication is
-- `eq_of_mem_primesOver_under_of_isStable`; the reverse implication uses the canonical
-- `Ideal.under_liesOver` witness for `P` over its contraction.

end Algebra.IsInvariant
