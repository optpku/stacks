/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- An assignment of sets of sieves is the underlying assignment of a Grothendieck topology
if and only if it is stable under pullback, satisfies local transitivity, and contains the
maximal sieve on every object. -/
theorem exists_sieves_eq_iff (sieves : ∀ X : C, Set (Sieve X)) :
    (∃ J : GrothendieckTopology C, J.sieves = sieves) ↔
      (∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X),
        S ∈ sieves X → S.pullback f ∈ sieves Y) ∧
      (∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ sieves X → ∀ R : Sieve X,
        (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X) ∧
      (∀ X : C, (⊤ : Sieve X) ∈ sieves X) := sorry

end CategoryTheory.GrothendieckTopology
