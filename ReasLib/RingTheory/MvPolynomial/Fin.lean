/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-Variable Coordinate Maps

This leaf owns the coordinate maps between multivariate polynomial rings in
`Fin (n + 1)` and `Fin n` variables.  It is independent of an ideal,
quotient, grading, or geometric interpretation.  In particular,
`evalHead 0` is the evaluation used for a first-variable quotient and
`evalHead 1` is the evaluation underlying dehomogenization.

The coordinate equivalences also provide shared support for Example 10.140.8
(`@stack 00TY`); the declarations below are neutral infrastructure rather
than source-labelled statements.

@stack 00TY

-/

universe u

namespace MvPolynomial.Fin

variable {A : Type u} [CommSemiring A]

/-- Evaluate the first variable of a polynomial in `Fin (n + 1)` variables at
`a`, while reindexing every successor variable by its tail index. -/
noncomputable def evalHead (a : A) (n : ℕ) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin n) A :=
  MvPolynomial.aeval
    (fun i : Fin (n + 1) ↦
      Fin.cases (MvPolynomial.C a) MvPolynomial.X i)

/-- Include a polynomial in `Fin n` variables as the polynomial in `Fin (n + 1)`
variables using only successor variables. -/
noncomputable def includeTail (n : ℕ) :
    MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  MvPolynomial.rename Fin.succ

/-- Substitute `a` for the first variable and retain every successor variable
in the ambient polynomial ring. -/
noncomputable def headSubst (a : A) (n : ℕ) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  (includeTail (A := A) n).comp (evalHead (A := A) a n)

/-- Evaluating the first variable at `a` sends `X 0` to the coefficient
constant `a`. -/
@[simp]
theorem evalHead_X_zero (a : A) (n : ℕ) :
    evalHead (A := A) a n (MvPolynomial.X (0 : Fin (n + 1))) = MvPolynomial.C a := by
  simp [evalHead]

/-- Evaluating the first variable at zero sends it to the zero polynomial. -/
@[simp]
theorem evalHead_zero_X_zero (n : ℕ) :
    evalHead (A := A) 0 n (MvPolynomial.X (0 : Fin (n + 1))) = 0 := by
  simp

/-- Evaluating the first variable at one sends it to the unit polynomial. -/
@[simp]
theorem evalHead_one_X_zero (n : ℕ) :
    evalHead (A := A) 1 n (MvPolynomial.X (0 : Fin (n + 1))) = 1 := by
  simp

/-- Evaluating the first variable at `a` sends a successor variable to its
tail counterpart. -/
@[simp]
theorem evalHead_X_succ (a : A) (n : ℕ) (j : Fin n) :
    evalHead (A := A) a n (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [evalHead]

/-- Head evaluation preserves coefficient constants. -/
@[simp]
theorem evalHead_C (a b : A) (n : ℕ) :
    evalHead (A := A) a n (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [evalHead]

/-- The tail inclusion sends a variable to the matching successor variable. -/
@[simp]
theorem includeTail_X (n : ℕ) (j : Fin n) :
    includeTail (A := A) n (MvPolynomial.X j) = MvPolynomial.X j.succ := by
  simp [includeTail]

/-- The tail inclusion preserves coefficient constants. -/
@[simp]
theorem includeTail_C (n : ℕ) (a : A) :
    includeTail (A := A) n (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [includeTail]

/-- The tail inclusion sends a monomial to the monomial whose exponent vector
is reindexed along `Fin.succ`. -/
@[simp]
theorem includeTail_monomial {n : ℕ} (d : Fin n →₀ ℕ) (a : A) :
    includeTail (A := A) n (MvPolynomial.monomial d a) =
      MvPolynomial.monomial (d.mapDomain Fin.succ) a := by
  exact MvPolynomial.rename_monomial Fin.succ d a

/-- Evaluating after the tail inclusion recovers the original tail polynomial. -/
@[simp]
theorem evalHead_includeTail (a : A) (n : ℕ) (p : MvPolynomial (Fin n) A) :
    evalHead (A := A) a n (includeTail (A := A) n p) = p := by
  induction p using MvPolynomial.induction_on with
  | C b => simp
  | add p q hp hq => simpa using congrArg₂ (.+.) hp hq
  | mul_X p i hp => simp [hp]

/-- As algebra homomorphisms, head evaluation after tail inclusion is the
identity of the tail polynomial ring. -/
theorem evalHead_comp_includeTail (a : A) (n : ℕ) :
    (evalHead (A := A) a n).comp (includeTail (A := A) n) =
      AlgHom.id A (MvPolynomial (Fin n) A) := by
  apply DFunLike.ext _ _
  intro p
  exact evalHead_includeTail a n p

/-- Applying head substitution first evaluates the head coordinate and then
restores the tail coordinates. -/
@[simp]
theorem headSubst_apply (a : A) (n : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    headSubst (A := A) a n p =
      includeTail (A := A) n (evalHead (A := A) a n p) := rfl

/-- Head substitution sends the first variable to the coefficient constant
`a`. -/
@[simp]
theorem headSubst_X_zero (a : A) (n : ℕ) :
    headSubst (A := A) a n (MvPolynomial.X (0 : Fin (n + 1))) = MvPolynomial.C a := by
  simp [headSubst]

/-- Head substitution fixes every successor variable. -/
@[simp]
theorem headSubst_X_succ (a : A) (n : ℕ) (j : Fin n) :
    headSubst (A := A) a n (MvPolynomial.X j.succ) = MvPolynomial.X j.succ := by
  simp [headSubst]

/-- Head substitution preserves coefficient constants. -/
@[simp]
theorem headSubst_C (a b : A) (n : ℕ) :
    headSubst (A := A) a n (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [headSubst]

/-- In the `finSuccEquiv` presentation, head evaluation is ordinary
univariate evaluation at the coefficient constant `a`. -/
theorem evalHead_eq_eval_finSuccEquiv (a : A) (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) A) :
    evalHead (A := A) a n p =
      Polynomial.eval (MvPolynomial.C a) (MvPolynomial.finSuccEquiv A n p) := by
  induction p using MvPolynomial.induction_on with
  | C b => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hp, MvPolynomial.finSuccEquiv_X_zero]
    · simp [hp, MvPolynomial.finSuccEquiv_X_succ]

/-- The canonical identification of a polynomial ring in `Fin (n + 1)` variables
with a univariate polynomial ring in the first `n` variables. -/
noncomputable def lastVariableEquiv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A) :=
  (MvPolynomial.renameEquiv A finSuccEquivLast).trans (MvPolynomial.optionEquivLeft A (Fin n))

/-- `lastVariableEquiv` sends each non-last coordinate to the corresponding constant polynomial. -/
@[simp]
theorem lastVariableEquiv_X_castSucc (n : ℕ) (i : Fin n) :
    lastVariableEquiv (A := A) n (MvPolynomial.X (Fin.castSucc i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [lastVariableEquiv]

/-- `lastVariableEquiv` sends the last coordinate to the polynomial variable. -/
@[simp]
theorem lastVariableEquiv_X_last (n : ℕ) :
    lastVariableEquiv (A := A) n (MvPolynomial.X (Fin.last n)) = Polynomial.X := by
  simp [lastVariableEquiv]

end MvPolynomial.Fin
