/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-free complement summands

This leaf owns the countably-generated freeness criterion used by the
Chapter 15 projective-module argument.

@stack 0591
-/

universe u v

namespace Module

/-- The complement-summand property from Lemma 10.85.2: after a finite free complemented summand
is removed, every element of the complementary summand lies in a free complemented summand. -/
@[stacks 0591 "finite-free complement summand property"]
def HasFiniteFreeComplementSummandProperty
    (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  ∀ ⦃N N' : Submodule R M⦄, IsCompl N N' → Module.Finite R N' → Module.Free R N' →
    ∀ x : N, ∃ F F' : Submodule R N, x ∈ F ∧ Module.Free R F ∧ IsCompl F F'

/-- Lemma 10.85.2: a countably generated module with the finite-free complement summand property
is free. -/
@[stacks 0591 "countably generated complement criterion for freeness"]
theorem free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hcg : CountablyGenerated R M)
    (hM : HasFiniteFreeComplementSummandProperty R M) :
    Module.Free R M := sorry

end Module
