/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.Noetherian
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.Polynomial
import StacksCheckRecall

/-!
# Lemma 88.2.2

Over a Noetherian ring, objects of `C'` are Noetherian, `C'` is stable under
quotients, and `I`-adic completions of finite type algebras (in particular
polynomial rings) lie in `C'`.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/- Lemma 88.2.2 (1) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Then every object of the category `C'` (`CommAlgCat.TopologicallyFiniteType A I`,
88.2.0.2) is Noetherian. -/
@[stacks 0AJQ] #check (Algebra.TopologicallyFiniteType.isNoetherianRing I :
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B],
    IsNoetherianRing B)

/- Lemma 88.2.2 (2) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
If `B` is an object of `C'` and `J ⊂ B` is an ideal, then `B ⧸ J` is an object
of `C'`. -/
@[stacks 0AJQ] #check (Algebra.TopologicallyFiniteType.instQuotient I :
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B]
    (J : Ideal B), Algebra.TopologicallyFiniteType I (B ⧸ J))

/- Lemma 88.2.2 (3) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
For a finite type `A`-algebra `C`, the `I`-adic completion `C^∧` is in `C'`. -/
@[stacks 0AJQ] #check (Algebra.TopologicallyFiniteType.instOfFiniteType I :
  ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C],
    Algebra.TopologicallyFiniteType I (AdicCompletion (I.map (algebraMap A C)) C))

/- Lemma 88.2.2 (4) Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
In particular the completion `A[x_1, …, x_r]^∧` is in `C'`. -/
@[stacks 0AJQ] #check (Algebra.TopologicallyFiniteType.instPolynomialCompletion
  (I := I) (hI := ⟨Ideal.fg_of_isNoetherianRing I⟩) :
  ∀ (r : ℕ), Algebra.TopologicallyFiniteType I (IAdicRestrictedPowerSeries (Fin r) I))
