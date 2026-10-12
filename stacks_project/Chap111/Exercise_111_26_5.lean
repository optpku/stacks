/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.EulerPoincare.Int
import StacksCheckRecall

@[expose] public section

/- Exercise 111.26.5
-/
@[stacks 02E3] #check (Module.EulerPoincareFunction.int_eq_intMultiple :
  ∀ φ : Module.EulerPoincareFunction.{0, 0} ℤ,
    φ = Module.EulerPoincareFunction.intMultiple
      (φ (CategoryTheory.ModuleCat.K0.Finite.rankOne ℤ)))

#check (Module.EulerPoincareFunction.intMultiple :
  ℤ → Module.EulerPoincareFunction.{0, 0} ℤ)

#check (Module.EulerPoincareFunction.intMultiple_eval :
  ∀ (n : ℤ) (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M],
    Module.EulerPoincareFunction.eval
      (Module.EulerPoincareFunction.intMultiple n) M =
      n * (Module.finrank ℤ M : ℤ))

#check (Module.EulerPoincareFunction.intMultiple_rankOne :
  ∀ n : ℤ,
    Module.EulerPoincareFunction.intMultiple n
        (CategoryTheory.ModuleCat.K0.Finite.rankOne ℤ) = n)

#check (Module.EulerPoincareFunction.int_eval_eq_mul_finrank :
  ∀ (φ : Module.EulerPoincareFunction.{0, 0} ℤ) (M : Type)
    [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M],
    Module.EulerPoincareFunction.eval φ M =
      φ (CategoryTheory.ModuleCat.K0.Finite.rankOne ℤ) *
        (Module.finrank ℤ M : ℤ))

#check (Module.EulerPoincareFunction.existsUnique_intMultiple :
  ∀ φ : Module.EulerPoincareFunction.{0, 0} ℤ,
    ∃! n : ℤ, φ = Module.EulerPoincareFunction.intMultiple n)
