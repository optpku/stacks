/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LinearPerturbation

/-!
# Smoothness of a linear perturbation family
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 93.17.2: Let `k` be a field and let `1 ≤ c ≤ n`. Given
`f : Fin c → MvPolynomial (Fin n) k`, form the linear perturbations `g f j` in
`k[aᵢⱼ][x₁,…,xₙ]`, let `Y` be the closed subscheme of `𝔸^{n+c(n+1)}_k` cut out by these
equations, and let `π : Y ⟶ 𝔸^{c(n+1)}_k` be projection onto the coefficient space.
Then there is a nonempty Zariski open of `𝔸^{c(n+1)}_k` over which `π` is smooth. -/
@[stacks 0E7U] #check
  (AlgebraicGeometry.LinearPerturbation.exists_isOpen_smooth :
    ∀ {k : Type u} [Field k] {n c : ℕ}, 1 ≤ c → c ≤ n →
      (f : Fin c → MvPolynomial (Fin n) k) →
        ∃ U : (AlgebraicGeometry.LinearPerturbation.coeffSpace k n c).Opens,
          Nonempty U ∧
            AlgebraicGeometry.Smooth (AlgebraicGeometry.LinearPerturbation.projection f ∣_ U))
