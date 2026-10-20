/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Constructible
import StacksCheckRecall

@[expose] public section

universe u v

open scoped Function

/- Exercise 111.15.2 (1): the complement of a constructible set is constructible. -/
@[stacks 0FJ5] #check (MvPolynomial.IsConstructible.compl :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} {s : Set (Fin n → k)},
    MvPolynomial.IsConstructible s → MvPolynomial.IsConstructible sᶜ)

/- Exercise 111.15.2 (2): a finite union of constructible sets is constructible. -/
@[stacks 0FJ5] #check (MvPolynomial.IsConstructible.iUnion :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {ι : Type u} [Finite ι] {s : ι → Set (Fin n → k)},
    (∀ i, MvPolynomial.IsConstructible (s i)) → MvPolynomial.IsConstructible (⋃ i, s i))

/- Exercise 111.15.2 (3): a finite intersection of constructible sets is constructible. -/
@[stacks 0FJ5] #check (MvPolynomial.IsConstructible.iInter :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {ι : Type u} [Finite ι] {s : ι → Set (Fin n → k)},
    (∀ i, MvPolynomial.IsConstructible (s i)) → MvPolynomial.IsConstructible (⋂ i, s i))

/- Exercise 111.15.2 (4): every constructible set is a finite disjoint union of basic
constructible pieces `Z ∩ nonvanishingSet f`. -/
@[stacks 0FJ5] #check (MvPolynomial.IsConstructible.exists_pairwiseDisjoint_isBasicConstructible :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} {s : Set (Fin n → k)},
    MvPolynomial.IsConstructible s →
      ∃ (ι : Type u) (_ : Finite ι) (E : ι → Set (Fin n → k)),
        Pairwise (Disjoint on E) ∧ s = (⋃ i, E i) ∧
          ∀ i, MvPolynomial.IsBasicConstructible (E i))
