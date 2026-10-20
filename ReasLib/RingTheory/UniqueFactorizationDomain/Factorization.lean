/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible factorizations and unique factorization

This leaf separates existence of irreducible factorizations from the condition that every
irreducible is prime.  The canonical conclusion remains Mathlib's
`UniqueFactorizationMonoid`; no second UFD structure is introduced.
-/

@[expose] public section

universe u

namespace UniqueFactorizationMonoid

variable {R : Type u} [CommSemiring R] [IsDomain R]

/-- A domain has irreducible factorizations when every nonzero nonunit is a finite product of
irreducible elements. -/
@[stacks 034T "irreducible factorizations"]
def HasIrreducibleFactorizations (R : Type u) [CommSemiring R] [IsDomain R] : Prop :=
  ∀ a : R, a ≠ 0 → ¬ IsUnit a →
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a

/-- Lemma 10.120.5 (Stacks `034T`): in a domain with irreducible factorizations, unique
factorization is equivalent to every irreducible element being prime. -/
@[stacks 034T]
theorem iff_forall_irreducible_prime
    (hfactor : HasIrreducibleFactorizations R) :
    UniqueFactorizationMonoid R ↔ ∀ a : R, Irreducible a → Prime a := sorry

end UniqueFactorizationMonoid
