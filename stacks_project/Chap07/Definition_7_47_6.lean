/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.GrothendieckTopology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable (C : Type u) [Category.{v} C]

/- Definition 7.47.6: a topology on a category C is an assignment U ↦ J U of
sieves on U such that (1) if f : V ⟶ U and S ∈ J U then S.pullback f ∈ J V,
(2) if S ∈ J U and S' is a sieve on U with S'.pullback f ∈ J V for every
f : V ⟶ U in S, then S' ∈ J U, and (3) the maximal sieve ⊤ belongs to J U.
Covering sieves are the members of J U. This is the canonical owner
GrothendieckTopology. -/
@[stacks 00Z4] #check (CategoryTheory.GrothendieckTopology.exists_sieves_eq_iff :
  ∀ sieves : ∀ X : C, Set (Sieve X),
    (∃ J : GrothendieckTopology C, J.sieves = sieves) ↔
      (∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X),
        S ∈ sieves X → S.pullback f ∈ sieves Y) ∧
      (∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ sieves X → ∀ R : Sieve X,
        (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X) ∧
      (∀ X : C, (⊤ : Sieve X) ∈ sieves X))

#check (CategoryTheory.GrothendieckTopology C : Type (max u v))

variable {X Y : C} {S : Sieve X}

#check (CategoryTheory.GrothendieckTopology.pullback_stable :
  ∀ (J : GrothendieckTopology C) (f : Y ⟶ X),
    S ∈ J X → S.pullback f ∈ J Y)

#check (CategoryTheory.GrothendieckTopology.transitive :
  ∀ (J : GrothendieckTopology C), S ∈ J X → ∀ R : Sieve X,
    (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) → R ∈ J X)

#check (CategoryTheory.GrothendieckTopology.top_mem :
  ∀ (J : GrothendieckTopology C) (X : C), (⊤ : Sieve X) ∈ J X)
