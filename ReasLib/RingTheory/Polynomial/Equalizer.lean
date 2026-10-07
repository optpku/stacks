module

public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equalizers of polynomial evaluations

@stack 00F1
@stack 00JG

This file packages the polynomials taking equal values at two points as a subalgebra. The
specialization to `0` and `1` is the equal-endpoint algebra used by several source items.
-/

@[expose] public section

noncomputable section

namespace Polynomial

universe u v

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The subalgebra of polynomials taking the same value at `x` and `y`. -/
@[stacks 00F1, stacks 00JG "polynomial evaluation equalizer"]
def evalEqualizer (x y : A) : Subalgebra R R[X] :=
  AlgHom.equalizer (aeval x) (aeval y)

/-- Membership in `evalEqualizer x y` means equality of the two evaluations. -/
@[simp, stacks 00F1, stacks 00JG "membership in a polynomial evaluation equalizer"]
theorem mem_evalEqualizer (x y : A) (f : R[X]) :
    f ∈ evalEqualizer x y ↔ aeval x f = aeval y f := by
  exact AlgHom.mem_equalizer (aeval x) (aeval y) f

/-- Equalizing evaluation at a point with itself imposes no condition. -/
@[simp]
theorem evalEqualizer_self (x : A) :
    evalEqualizer (R := R) x x = ⊤ := by
  ext f
  simp

/-- The polynomial evaluation equalizer is symmetric in its two points. -/
theorem evalEqualizer_comm (x y : A) :
    evalEqualizer (R := R) x y = evalEqualizer (R := R) y x := by
  ext f
  simp [eq_comm]

namespace EvalEqualizer

/-- Evaluation at the first point, restricted to the polynomial evaluation equalizer. -/
@[stacks 00JG "evaluation on a polynomial evaluation equalizer"]
def eval (x y : A) : evalEqualizer (R := R) x y →ₐ[R] A :=
  (aeval x).comp (evalEqualizer (R := R) x y).val

/-- Evaluation on the equalizer agrees with polynomial evaluation at its first point. -/
@[simp]
theorem eval_apply (x y : A) (f : evalEqualizer (R := R) x y) :
    eval x y f = aeval x (f : R[X]) := by
  rfl

/-- On the evaluation equalizer, evaluation at either point has the same value. -/
theorem eval_eq_right (x y : A) (f : evalEqualizer (R := R) x y) :
    eval x y f = aeval y (f : R[X]) := by
  rw [eval_apply, ← mem_evalEqualizer]
  exact f.property

end EvalEqualizer

/-- The subalgebra of polynomials taking the same value at `0` and `1`. -/
@[stacks 00F1, stacks 00JG "equal-endpoint polynomial algebra"]
def equalEndpoint (R : Type u) [CommSemiring R] : Subalgebra R R[X] :=
  evalEqualizer (0 : R) (1 : R)

/-- Membership in the equal-endpoint algebra is equality at `0` and `1`. -/
@[simp, stacks 00F1, stacks 00JG "membership in the equal-endpoint algebra"]
theorem mem_equalEndpoint (f : R[X]) :
    f ∈ equalEndpoint R ↔ f.eval 0 = f.eval 1 := by
  change aeval (0 : R) f = aeval (1 : R) f ↔ _
  rfl

namespace EqualEndpoint

/-- Evaluation at the common endpoint of an equal-endpoint polynomial. -/
@[stacks 00JG "common-endpoint evaluation"]
def eval (R : Type u) [CommSemiring R] : equalEndpoint R →ₐ[R] R :=
  EvalEqualizer.eval 0 1

/-- Evaluation on the equal-endpoint algebra is evaluation at zero. -/
@[simp]
theorem eval_apply (f : equalEndpoint R) :
    eval R f = (f : R[X]).eval 0 := by
  rfl

/-- The canonical action of the equal-endpoint algebra on its coefficient ring. -/
@[stacks 00JG "common-endpoint algebra structure"]
noncomputable instance endpointAlgebra : Algebra (equalEndpoint R) R :=
  (eval R).toRingHom.toAlgebra

/-- The canonical algebra map from the equal-endpoint algebra is evaluation at zero. -/
@[simp]
theorem algebraMap_apply (f : equalEndpoint R) :
    algebraMap (equalEndpoint R) R f = (f : R[X]).eval 0 := by
  rfl

end EqualEndpoint

end Polynomial
