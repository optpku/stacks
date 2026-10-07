module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_17_2_Perturbation

/-!
# Smoothness of a linear perturbation family
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LinearPerturbation

/-- Lemma 93.17.2: Let `k` be a field and let `1 ≤ c ≤ n`. Given
`f : Fin c → MvPolynomial (Fin n) k`, form the linear perturbations `g f j` in
`k[aᵢⱼ][x₁,…,xₙ]`, let `Y` be the closed subscheme of `𝔸^{n+c(n+1)}_k` cut out by these
equations, and let `π : Y ⟶ 𝔸^{c(n+1)}_k` be projection onto the coefficient space.
Then there is a nonempty Zariski open of `𝔸^{c(n+1)}_k` over which `π` is smooth. -/
@[stacks 0E7U]
theorem exists_isOpen_smooth {k : Type u} [Field k] {n c : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) k) :
    ∃ U : (coeffSpace k n c).Opens, Nonempty U ∧ Smooth (projection f ∣_ U) :=
  sorry

end AlgebraicGeometry.LinearPerturbation
