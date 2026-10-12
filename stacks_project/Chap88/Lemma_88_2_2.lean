/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Lemma_88_2_2_Completion
public import stacks_project.Chap88.Lemma_88_2_2_Noetherian
public import stacks_project.Chap88.Lemma_88_2_2_Quotient

/-!
# Lemma 88.2.2

Over a Noetherian ring, objects of `C'` are Noetherian, `C'` is stable under
quotients, and `I`-adic completions of finite type algebras (in particular
polynomial rings) lie in `C'`.
-/

@[expose] public section

universe u

namespace Algebra.TopologicallyFiniteType

/-- Lemma 88.2.2 (1) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Then every object of the category `C'` (`CommAlgCat.TopologicallyFiniteType A I`,
88.2.0.2) is Noetherian. -/
@[stacks 0AJQ]
theorem isNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    IsNoetherianRing B :=
  sorry

/-- Lemma 88.2.2 (2) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
If `B` is an object of `C'` and `J ⊂ B` is an ideal, then `B ⧸ J` is an object
of `C'`. -/
@[stacks 0AJQ]
theorem quotient {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] (J : Ideal B) :
    TopologicallyFiniteType I (B ⧸ J) :=
  sorry

/-- Lemma 88.2.2 (3) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
For a finite type `A`-algebra `C`, the `I`-adic completion `C^∧` is in `C'`. -/
@[stacks 0AJQ]
theorem adicCompletion_ofFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    TopologicallyFiniteType I (AdicCompletion (I.map (algebraMap A C)) C) :=
  sorry

/-- Lemma 88.2.2 (4) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
In particular the completion `A[x_1, …, x_r]^∧` is in `C'`. -/
@[stacks 0AJQ]
theorem adicCompletion_mvPolynomial {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (r : ℕ) :
    TopologicallyFiniteType I (IAdicRestrictedPowerSeries (Fin r) I) :=
  sorry

end Algebra.TopologicallyFiniteType
