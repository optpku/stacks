/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.Algebra.Algebra.Tower

/-!
# Restricting Differential-Operator Order Bounds

This leaf records the two general restriction operations on the recursive
`LinearMap.IsDifferentialOperatorOfOrder` predicate.  They are independent of
principal parts: later representing constructions should consume these lemmas
rather than reproduce their scalar-commutator inductions.
-/

@[expose] public section

universe u v w x y

namespace LinearMap.IsDifferentialOperatorOfOrder

section RestrictScalars

variable {R : Type u} {A : Type v} {S : Type w} {X : Type x} {Y : Type y}
variable [CommSemiring R] [Semiring A] [Semiring S] [Algebra R A]
variable [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]
variable [Module S X] [SMulCommClass S R X] [SMulCommClass S A X]
variable [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower R A Y]
variable [Module S Y] [SMulCommClass S R Y] [SMulCommClass S A Y]

/-- Restricting the linearity ring of a differential operator preserves its
order bound for the same scalar action. -/
theorem restrictScalars {D : X →ₗ[A] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    (D.restrictScalars R).IsDifferentialOperatorOfOrder S k := sorry

end RestrictScalars

section RestrictAlgebra

variable {R : Type u} {A : Type v} {S : Type w} {X : Type x} {Y : Type y}
variable [Semiring R] [CommSemiring A] [Semiring S] [Algebra A S]
variable [AddCommGroup X] [Module R X] [Module A X] [Module S X]
variable [SMulCommClass A R X] [SMulCommClass S R X] [IsScalarTower A S X]
variable [AddCommGroup Y] [Module R Y] [Module A Y] [Module S Y]
variable [SMulCommClass A R Y] [SMulCommClass S R Y] [IsScalarTower A S Y]

/-- An order bound for the scalar action of an `A`-algebra `S` restricts to
the induced action of `A`. -/
theorem restrictAlgebra {D : X →ₗ[R] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder A k := sorry

end RestrictAlgebra

end LinearMap.IsDifferentialOperatorOfOrder
