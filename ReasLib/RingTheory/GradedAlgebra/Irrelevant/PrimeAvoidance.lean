/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite homogeneous-prime avoidance

@stack 00JS

This leaf extracts a positive-degree homogeneous element while avoiding a
finite family of homogeneous prime ideals.
-/

universe u v

namespace HomogeneousIdeal

/-- Lemma 10.57.6 (00JS): a homogeneous ideal below the irrelevant ideal and
not contained in any of finitely many homogeneous primes contains a
positive-degree homogeneous element avoiding all those primes. -/
@[stacks 00JS]
theorem exists_posDegree_mem_avoid_primes
    {A : Type u} {sigma : Type v}
    [CommRing A] [SetLike sigma A] [AddSubmonoidClass sigma A]
    (Agrade : ℕ → sigma) [GradedRing Agrade]
    {r : ℕ} (I : HomogeneousIdeal Agrade)
    (p : Fin r → HomogeneousIdeal Agrade)
    (hprime : ∀ i, (p i).toIdeal.IsPrime)
    (hI_irrelevant : I ≤ irrelevant Agrade)
    (havoid : ∀ i, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ Agrade d ∧ ∀ i, x ∉ p i := sorry

end HomogeneousIdeal
