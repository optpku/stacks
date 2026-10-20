/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed families of subalgebras from finite covers

This leaf turns finite-subset covers by finitely generated subalgebras into a
canonical directed subtype family.  It is independent of the property carried
by the stages, so geometric applications depend on this layer rather than
recreating choice-based finset-indexed families.

@stack 07BV
-/

@[expose] public section

namespace Subalgebra

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A property of subalgebras that covers every finite subset has a nonempty
subtype of property-bearing subalgebras. -/
@[stacks 07BV "nonempty subalgebra cover"]
theorem nonempty_subtype_of_finset_cover
    (P : Subalgebra R A → Prop)
    (hcover : ∀ E : Finset A, ∃ B : Subalgebra R A, P B ∧ (E : Set A) ⊆ B) :
    Nonempty {B : Subalgebra R A // P B} := sorry

/-- If every property-bearing subalgebra is finitely generated and the property
covers finite subsets, the canonical subtype family is directed by inclusion. -/
@[stacks 07BV "directed subalgebra cover"]
theorem directed_subtype_of_finset_cover
    (P : Subalgebra R A → Prop)
    (hfg : ∀ B : Subalgebra R A, P B → B.FG)
    (hcover : ∀ E : Finset A, ∃ B : Subalgebra R A, P B ∧ (E : Set A) ⊆ B) :
    Directed (· ≤ ·) (fun B : {B : Subalgebra R A // P B} => B.1) := sorry

/-- A property that covers every finite subset has property-bearing
subalgebras whose supremum is the whole ambient algebra. -/
@[stacks 07BV "exhaustive subalgebra cover"]
theorem iSup_subtype_eq_top_of_finset_cover
    (P : Subalgebra R A → Prop)
    (hcover : ∀ E : Finset A, ∃ B : Subalgebra R A, P B ∧ (E : Set A) ⊆ B) :
    iSup (fun B : {B : Subalgebra R A // P B} => B.1) = (⊤ : Subalgebra R A) := sorry

/-- A finite-subset cover by finitely generated property-bearing subalgebras
admits a nonempty directed exhaustive family of such subalgebras. -/
@[stacks 07BV "directed exhaustive subalgebra family"]
theorem exists_directed_family_of_finset_cover
    (P : Subalgebra R A → Prop)
    (hfg : ∀ B : Subalgebra R A, P B → B.FG)
    (hcover : ∀ E : Finset A, ∃ B : Subalgebra R A, P B ∧ (E : Set A) ⊆ B) :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra R A), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, P (S i)) ∧ iSup S = (⊤ : Subalgebra R A) := sorry

end Subalgebra
