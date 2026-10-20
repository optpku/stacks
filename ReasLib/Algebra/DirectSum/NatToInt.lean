module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Action.NatInt

/-!
# Extending a Natural Grading to the Integers

An `ℕ`-indexed direct sum has a canonical `ℤ`-grading obtained by putting the
negative components equal to zero.  This file packages that construction,
its component equivalences, and its direct-sum decomposition.

The degree action is imported from `AddAction.natInt`; this leaf owns only the
direct-sum transport.  Keeping those owners separate lets graded-module and direct-sum users
share one action instance without importing the other construction.
-/

@[expose] public section

noncomputable section

universe u v w

namespace DirectSum

variable {R : Type u} [Semiring R]
variable (A : ℕ → Type v) [∀ n, AddCommMonoid (A n)] [∀ n, Module R (A n)]

/-- The inclusion of one summand into a direct sum is injective. -/
theorem lof_injective (n : ℕ) :
    Function.Injective (DirectSum.lof R ℕ A n) := sorry

/-- A direct-sum summand is canonically linearly equivalent to the range of
its inclusion. -/
noncomputable def lofEquivRange (n : ℕ) :
    A n ≃ₗ[R] LinearMap.range (DirectSum.lof R ℕ A n) :=
  LinearEquiv.ofInjective (DirectSum.lof R ℕ A n) (lof_injective A n)

/-- The integer grading obtained from an `ℕ`-indexed direct sum by extending
the grading by zero in negative degrees. -/
@[stacks 00K8 "nonnegative grading extended to the integers"]
def natToIntGrading (d : ℤ) : Submodule R (DirectSum ℕ A) :=
  if 0 ≤ d then LinearMap.range (DirectSum.lof R ℕ A d.toNat) else ⊥

/-- In a nonnegative integer degree, `natToIntGrading` is the range of the
corresponding natural-number summand. -/
theorem natToIntGrading_eq_range_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    natToIntGrading (R := R) A d =
      LinearMap.range (DirectSum.lof R ℕ A d.toNat) := sorry

/-- In a negative degree, `natToIntGrading` is zero. -/
theorem natToIntGrading_eq_bot_of_neg {d : ℤ} (hd : d < 0) :
    natToIntGrading (R := R) A d = ⊥ := sorry

/-- At the integer image of `n`, `natToIntGrading` is the range of the
original degree-`n` summand. -/
theorem natToIntGrading_nat_eq_range (n : ℕ) :
    natToIntGrading (R := R) A (n : ℤ) =
      LinearMap.range (DirectSum.lof R ℕ A n) := sorry

/-- The original degree-`n` summand is canonically equivalent to degree `n`
of the integer-extended grading. -/
@[stacks 00K8 "natural component in the integer extension"]
noncomputable def natToIntGradingEquiv (n : ℕ) :
    A n ≃ₗ[R] natToIntGrading (R := R) A (n : ℤ) :=
  (lofEquivRange (R := R) A n).trans
    (LinearEquiv.ofEq _ _ (natToIntGrading_nat_eq_range (R := R) A n).symm)

/-- The integer-grading component equivalence preserves the ambient
direct-sum representative. -/
@[stacks 00K8 "integer extension component inclusion", simp]
theorem natToIntGradingEquiv_coe (n : ℕ) (x : A n) :
    ((natToIntGradingEquiv (R := R) A n x :
        natToIntGrading (R := R) A (n : ℤ)) : DirectSum ℕ A) =
      DirectSum.lof R ℕ A n x := sorry

/-- The integer extension of the natural grading is an internal direct-sum
decomposition. -/
@[stacks 00K8 "nonnegative grading extended to the integers"]
theorem natToIntGrading_isInternal :
    DirectSum.IsInternal (natToIntGrading (R := R) A) := sorry

/-- The integer extension carries its canonical decomposition instance. -/
@[stacks 00K8 "nonnegative grading extension decomposition"]
noncomputable instance natToIntGradingDecomposition :
    DirectSum.Decomposition (natToIntGrading (R := R) A) :=
  (natToIntGrading_isInternal (R := R) A).chooseDecomposition

end DirectSum
