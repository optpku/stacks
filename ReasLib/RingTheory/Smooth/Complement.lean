/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Locus

/-!
# Smoothness over the complement of an ideal's zero locus

Smoothness over an ideal complement is containment of its inverse image in the
smooth locus, and can be tested on principal localizations for finitely presented algebras.
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace Algebra

/-- The spectrum of an algebra is smooth over the complement of `V(I)` when the
complement of `V(I B)` is contained in its smooth locus. -/
def IsSmoothOverComplement {A : Type u} [CommRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  (zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ smoothLocus A B

/-- Smoothness over the complement of `V(I)` is containment of the complement of
`V(I B)` in the smooth locus. -/
theorem isSmoothOverComplement_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    IsSmoothOverComplement I B ↔
      (zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ smoothLocus A B :=
  by rfl

/-- A finitely presented algebra is smooth over the complement of `V(I)` if and
only if its principal localization at every element of `I B` is smooth. -/
theorem isSmoothOverComplement_iff_forall_mem_map_smooth
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (I : Ideal A) :
    IsSmoothOverComplement I B ↔
      ∀ g ∈ I.map (algebraMap A B), Smooth A (Localization.Away g) :=
  sorry

end Algebra
