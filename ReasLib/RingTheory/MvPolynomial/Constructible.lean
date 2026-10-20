/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.AlgebraicSet

@[expose] public section

universe u v

open scoped Function

namespace MvPolynomial

section

variable {σ : Type v} {k : Type u} [Field k]

/-- The nonvanishing locus of a polynomial `f`, as a subset of `σ → k`. -/
def nonvanishingSet (f : MvPolynomial σ k) : Set (σ → k) :=
  {x | aeval x f ≠ 0}

/-- A point lies in `nonvanishingSet f` iff `aeval x f` is nonzero. -/
theorem mem_nonvanishingSet {f : MvPolynomial σ k} {x : σ → k} :
    x ∈ nonvanishingSet f ↔ aeval x f ≠ 0 := sorry

/-- The nonvanishing locus of `f` is the complement of the principal zero locus of `f`. -/
theorem nonvanishingSet_eq_compl_zeroLocus (f : MvPolynomial σ k) :
    nonvanishingSet f = (zeroLocus k (Ideal.span {f}))ᶜ := sorry

/-- A basic constructible piece is an algebraic set cut by a polynomial nonvanishing locus. -/
def IsBasicConstructible (s : Set (σ → k)) : Prop :=
  ∃ (Z : Set (σ → k)) (f : MvPolynomial σ k), IsAlgebraicSet Z ∧ s = Z ∩ nonvanishingSet f

/-- Basic constructible sets are intersections of an algebraic set with a nonvanishing locus. -/
theorem isBasicConstructible_iff {s : Set (σ → k)} :
    IsBasicConstructible s ↔
      ∃ (Z : Set (σ → k)) (f : MvPolynomial σ k),
        IsAlgebraicSet Z ∧ s = Z ∩ nonvanishingSet f := sorry

/-- A subset of `σ → k` is constructible when it is a finite union of basic constructible pieces. -/
def IsConstructible (s : Set (σ → k)) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (E : ι → Set (σ → k)),
    s = (⋃ i, E i) ∧ ∀ i, IsBasicConstructible (E i)

/-- A basic constructible set is constructible. -/
theorem isConstructible_of_isBasicConstructible {s : Set (σ → k)}
    (hs : IsBasicConstructible s) : IsConstructible s := sorry

/-- Constructible sets are precisely the finite unions of basic constructible pieces. -/
theorem isConstructible_iff {s : Set (σ → k)} :
    IsConstructible s ↔
      ∃ (ι : Type u) (_ : Finite ι) (E : ι → Set (σ → k)),
        s = (⋃ i, E i) ∧ ∀ i, IsBasicConstructible (E i) := sorry

end

namespace IsConstructible

/-- The complement of a constructible set in finite-dimensional affine space over an
algebraically closed field is constructible. -/
theorem compl {k : Type u} [Field k] [IsAlgClosed k] {σ : Type v} [Finite σ]
    {s : Set (σ → k)} (hs : IsConstructible s) : IsConstructible sᶜ := sorry

/-- A finite union of constructible sets in finite-dimensional affine space over an
algebraically closed field is constructible. -/
theorem iUnion {k : Type u} [Field k] [IsAlgClosed k] {σ : Type v} [Finite σ]
    {ι : Type u} [Finite ι] {s : ι → Set (σ → k)} (hs : ∀ i, IsConstructible (s i)) :
    IsConstructible (⋃ i, s i) := sorry

/-- A finite intersection of constructible sets in finite-dimensional affine space over an
algebraically closed field is constructible. -/
theorem iInter {k : Type u} [Field k] [IsAlgClosed k] {σ : Type v} [Finite σ]
    {ι : Type u} [Finite ι] {s : ι → Set (σ → k)} (hs : ∀ i, IsConstructible (s i)) :
    IsConstructible (⋂ i, s i) := sorry

/-- Every constructible set in finite-dimensional affine space over an algebraically closed
field is a finite disjoint union of basic constructible pieces `Z ∩ nonvanishingSet f`. -/
theorem exists_pairwiseDisjoint_isBasicConstructible
    {k : Type u} [Field k] [IsAlgClosed k] {σ : Type v} [Finite σ] {s : Set (σ → k)}
    (hs : IsConstructible s) :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Set (σ → k)),
      Pairwise (Disjoint on E) ∧ s = (⋃ i, E i) ∧ ∀ i, IsBasicConstructible (E i) := sorry

end IsConstructible

end MvPolynomial
