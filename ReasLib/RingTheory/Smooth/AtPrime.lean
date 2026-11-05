/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.AtPrime

@[expose] public section

/-!
# Smoothness at a Prime

The Stacks-style local formulation of smoothness: an algebra is smooth at a
prime when it is smooth on some basic open neighbourhood of that prime.

@stack 00TB
-/

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.137.10: `R → S` is smooth at `q` when a basic open neighbourhood of `q`
is smooth over `R`. -/
@[stacks 00TB]
def SmoothAtPrime (q : PrimeSpectrum S) : Prop :=
  RingHom.AtPrime (fun f ↦ f.Smooth) (algebraMap R S) q

namespace SmoothAtPrime

/-- The source-facing principal-open witness form of `SmoothAtPrime`. -/
@[stacks 00TB "smoothness on a principal-open neighborhood of a prime"]
theorem iff_exists_away (q : PrimeSpectrum S) :
    Algebra.SmoothAtPrime R S q ↔
      ∃ g : S, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g) := by
  unfold Algebra.SmoothAtPrime RingHom.AtPrime
  constructor
  · rintro ⟨g, hg, hSmooth⟩
    refine ⟨g, hg, ?_⟩
    rw [← RingHom.smooth_algebraMap]
    convert hSmooth using 1 <;> ext <;> rfl
  · rintro ⟨g, hg, hSmooth⟩
    refine ⟨g, hg, ?_⟩
    rw [← RingHom.smooth_algebraMap] at hSmooth
    convert hSmooth using 1 <;> ext <;> rfl

/-- For a finitely presented algebra, Stacks-style smoothness at a prime agrees with mathlib's
canonical `IsSmoothAt` predicate. -/
theorem iff_isSmoothAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    Algebra.SmoothAtPrime R S q ↔ IsSmoothAt R q.asIdeal := by
  rw [iff_exists_away]
  constructor
  · rintro ⟨g, hg, hSmooth⟩
    change q ∈ smoothLocus R S
    exact (basicOpen_subset_smoothLocus_iff_smooth.mpr hSmooth) (by simpa using hg)
  · intro hSmooth
    -- Local instance justification (proof-local temporary data): the reverse implication gives
    -- `hSmooth` explicitly, but `exists_notMem_smooth` consumes the local predicate as a class.
    letI : IsSmoothAt R q.asIdeal := hSmooth
    exact IsSmoothAt.exists_notMem_smooth R q.asIdeal

end SmoothAtPrime

end Algebra
