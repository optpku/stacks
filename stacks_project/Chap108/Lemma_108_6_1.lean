/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_6_1_ProperOver
public import stacks_project.Chap108.Lemma_108_6_1_Projective

/-!
# Lemma 108.6.1

The Hilbert Quot algebraic space of finite free quotients on `P^n` over
`Spec(ℤ)` is proper over `Spec(ℤ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 108.6.1: for `n ≥ 0`, `r ≥ 1`, and Hilbert polynomial `P`, the algebraic
space `Quot^P` of quotients of `𝒪_{P^n_ℤ}^{⊕ r}` with Hilbert polynomial `P` is
proper over `Spec(ℤ)`. -/
@[stacks 0DPA]
theorem quotHilbert_projective_isProperOver (n r : ℕ) (hr : 1 ≤ r) (P : ℤ → ℤ) :
    IsProperOver (quotHilbert_projective n r P).toFunctor :=
  sorry

/-- Properness of `quotHilbert_projective` means some representing morphism of
algebraic spaces over `Spec(ℤ)` is proper. -/
theorem quotHilbert_projective_isProperOver_spec (n r : ℕ) (hr : 1 ≤ r)
    (P : ℤ → ℤ) :
    IsProperOver (quotHilbert_projective n r P).toFunctor ↔
      ∃ (X : AlgebraicSpace (⊤_ Scheme.{u})) (π : X ⟶ specSpace),
        Proper π ∧
          Nonempty ((quotHilbert_projective n r P).toFunctor ≅ yonedaOver π) :=
  sorry

/-- A rational polynomial taking integer values at integers yields a Hilbert
Quot functor proper over `Spec(ℤ)`. -/
theorem quotHilbert_projective_ofIntegerValued_isProperOver (n r : ℕ)
    (hr : 1 ≤ r) (P : Polynomial ℚ)
    (hP : ∀ k : ℤ, (P.eval (k : ℚ)).den = 1) :
    IsProperOver (quotHilbert_projective n r (ofIntegerValued P hP)).toFunctor :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
