module

public import stacks_project.Chap88.Lemma_88_2_1_Limit
public import stacks_project.Chap88.Lemma_88_2_1_Presentation

/-!
# Lemma 88.2.1

The inverse-limit functor `C ⟶ C'` is a quasi-inverse of `toAdicSystem`.
Polynomial completions `A[x_1, …, x_r]^∧` lie in `C'`, and every object of
`C'` is a quotient of such a completion.
-/

@[expose] public section

open CategoryTheory
open CommAlgCat.TopologicallyFiniteType
open Algebra.TopologicallyFiniteType

universe u

variable {A : Type u} [CommRing A]

/-- Lemma 88.2.1 (1) Let A be a ring and let I ⊂ A be a finitely generated
ideal. The functor C ⟶ C', (B n) ↦ lim B n is a quasi-inverse to
(88.2.0.3). -/
@[stacks 0AJP]
noncomputable def inverseLimitQuasiInverse (I : Ideal A) (hI : I.FG) :
    (toAdicSystem I).QuasiInverse :=
  AdicAlgebraSystem.limitFunctorQuasiInverse I hI

/-- The inverse functor in Lemma 88.2.1 (1) is the inverse-limit functor. -/
theorem inverseLimitQuasiInverse_inverse (I : Ideal A) (hI : I.FG) :
    (inverseLimitQuasiInverse I hI).inverse =
      AdicAlgebraSystem.limitFunctor I hI :=
  sorry

/-- Lemma 88.2.1 (2) The completions A[x_1, …, x_r]^∧ are in C'. -/
@[stacks 0AJP]
noncomputable def mvPolynomialCompletion (I : Ideal A) (hI : I.FG) (r : ℕ) :
    CommAlgCat.TopologicallyFiniteType.{u} A I :=
  CommAlgCat.TopologicallyFiniteType.mvPolynomialCompletion I hI r

/-- The underlying algebra of Lemma 88.2.1 (2) is the `I`-adic restricted
power series ring on `r` variables. -/
theorem mvPolynomialCompletion_obj (I : Ideal A) (hI : I.FG) (r : ℕ) :
    (_root_.mvPolynomialCompletion I hI r).obj =
      CommAlgCat.of A (IAdicRestrictedPowerSeries (Fin r) I) :=
  sorry

/-- Lemma 88.2.1 (3) Any object of C' is of the form
B = A[x_1, …, x_r]^∧ / J for some ideal J ⊂ A[x_1, …, x_r]^∧. -/
@[stacks 0AJP]
theorem exists_isQuotient_polynomialCompletion (I : Ideal A) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.TopologicallyFiniteType I B] :
    ∃ (r : ℕ) (J : Ideal (IAdicRestrictedPowerSeries (Fin r) I)),
      Nonempty (B ≃ₐ[A] IAdicRestrictedPowerSeries (Fin r) I ⧸ J) :=
  sorry
