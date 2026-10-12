/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.EulerPoincare
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.PID
import Mathlib.Tactic.CrossRefAttribute

/-!
# Euler-Poincaré functions over the integers

Euler-Poincaré functions on finitely generated integer modules are classified by
their value on the rank-one free module.
-/

@[expose] public section

noncomputable section

open CategoryTheory.ModuleCat

namespace Module.EulerPoincareFunction

/-- The Euler-Poincaré function on finite integer modules given by `n` times generic rank. -/
def intMultiple (n : ℤ) : EulerPoincareFunction.{0, 0} ℤ :=
  n • K0.Finite.genericRank.{0, 0} ℤ

/-- `intMultiple n` evaluates on a finitely generated integer module as `n` times its rank. -/
theorem intMultiple_eval (n : ℤ) (M : Type) [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] :
    eval (intMultiple n) M = n * (Module.finrank ℤ M : ℤ) :=
  sorry

/-- The value of `intMultiple n` on the rank-one free module is `n`. -/
theorem intMultiple_rankOne (n : ℤ) :
    intMultiple n (K0.Finite.rankOne ℤ) = n :=
  sorry

/-- Every Euler-Poincaré function on finite integer modules is an integer multiple of generic rank. -/
@[stacks 02E3]
theorem int_eq_intMultiple (φ : EulerPoincareFunction.{0, 0} ℤ) :
    φ = intMultiple (φ (K0.Finite.rankOne ℤ)) :=
  sorry

/-- The value of an Euler-Poincaré function on a module is its rank-one value times the rank. -/
theorem int_eval_eq_mul_finrank (φ : EulerPoincareFunction.{0, 0} ℤ)
    (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] :
    eval φ M = φ (K0.Finite.rankOne ℤ) * (Module.finrank ℤ M : ℤ) :=
  sorry

/-- Euler-Poincaré functions on finite integer modules are uniquely parametrized by `intMultiple`. -/
theorem existsUnique_intMultiple (φ : EulerPoincareFunction.{0, 0} ℤ) :
    ∃! n : ℤ, φ = intMultiple n :=
  sorry

end EulerPoincareFunction

end Module
