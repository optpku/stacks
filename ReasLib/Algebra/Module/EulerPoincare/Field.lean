/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length
public import ReasLib.Algebra.Module.EulerPoincare

/-!
# Euler-Poincaré functions over fields

Euler-Poincaré functions on finite-dimensional vector spaces over a field are precisely integer
multiples of dimension.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.ModuleCat

namespace Module.EulerPoincareFunction

variable (k : Type u) [Field k]

/-- The integer multiple of the finite-module length homomorphism with coefficient `n`. -/
def ofInt (n : ℤ) : EulerPoincareFunction.{u, u} k :=
  (AddMonoidHom.mulLeft n).comp (K0.finiteLength k)

/-- The integer multiple with coefficient `n` evaluates on a finite module as `n` times its
finite dimension. -/
theorem ofInt_eval (n : ℤ) (M : Type u) [AddCommGroup M] [Module k M] [Module.Finite k M] :
    eval (ofInt k n) M = n * Module.finrank k M := sorry

/-- The coefficient of the integer multiple with coefficient `n` is `n` on the field itself. -/
theorem ofInt_eval_field (n : ℤ) :
    eval (ofInt k n) k = n := sorry

/-- Every Euler-Poincaré function on finite modules over a field is an integer multiple of
dimension, with coefficient given by its value on the field. -/
@[stacks 02E2]
theorem eq_ofInt {k : Type u} [Field k] (φ : EulerPoincareFunction.{u, u} k) :
    φ = ofInt k (eval φ k) := sorry

/-- Every Euler-Poincaré function evaluates on a finite module as its value on the field times
the module's finite dimension. -/
theorem eval_eq_mul_finrank {k : Type u} [Field k] (φ : EulerPoincareFunction.{u, u} k)
    (M : Type u) [AddCommGroup M] [Module k M] [Module.Finite k M] :
    eval φ M = eval φ k * Module.finrank k M := sorry

end Module.EulerPoincareFunction
