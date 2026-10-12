/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import ReasLib.RingTheory.Ideal.Square
import StacksCheckRecall

@[expose] public section

universe u

namespace AdicCompletion

/- 110.7.0.1: a typical element of `(m') ^ 2` in the `m`-adic completion of
`R = k[x_1, x_2, …]` is a finite sum `∑ i, f i * g i` with `f i, g i` of vanishing
constant term. Here `k` is a field, `R = MvPolynomial ℕ k`,
`m = MvPolynomial.idealOfVars ℕ k`, the completion is `AdicCompletion m R`, and
`m' = RingHom.ker (AdicCompletion.evalOneₐ m).toRingHom`. -/
@[stacks 05JB] #check (Ideal.exists_sum_mul_of_mem_sq :
    ∀ {k : Type u} [Field k]
      {x : AdicCompletion (MvPolynomial.idealOfVars ℕ k) (MvPolynomial ℕ k)},
    let R := MvPolynomial ℕ k
    let m := MvPolynomial.idealOfVars ℕ k
    let m' := RingHom.ker (evalOneₐ m).toRingHom
    x ∈ m' ^ 2 →
      ∃ (t : ℕ) (f g : Fin t → AdicCompletion m R),
        (∀ i, f i ∈ m') ∧ (∀ i, g i ∈ m') ∧ x = ∑ i, f i * g i)

end AdicCompletion
