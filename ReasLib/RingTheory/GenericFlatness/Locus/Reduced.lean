/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Locus.Local

/-!
# Density of the generic-flatness locus over reduced rings

This is the reusable reduced-base form of the generic-flatness theorem.

@stack 051Z
-/

@[expose] public section

universe u v w

namespace GenericFlatness

/-- For a finite-type algebra and a finite module over a reduced base ring, the generic-flatness
good locus is dense. -/
@[stacks 051Z "density of the generic-flatness locus over a reduced ring"]
theorem dense_of_finiteType_finiteModule_reduced
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R] :
    Dense (goodLocus R S M) := sorry

/-- Lemma 10.118.7: over a reduced base, generic flatness is witnessed by an
open dense set whose points admit principal-open neighborhoods satisfying the
localization condition. -/
@[stacks 051Z "open dense generic-flatness locus with principal witnesses"]
theorem exists_open_dense_with_localizationCondition
    {R : Type u} [CommRing R] [IsReduced R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M] :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ Dense U ∧
      ∀ u ∈ U, ∃ f : R,
        u ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ U ∧
        LocalizationCondition R S M f := sorry

end GenericFlatness
