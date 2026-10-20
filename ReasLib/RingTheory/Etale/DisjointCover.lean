/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.RingTheory.Etale.IdempotentLift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale-local lifting of disjoint spectral covers

@stack 07LZ

Finite disjoint open covers of the spectrum of a quotient lift after an etale base change which
does not alter that quotient.
-/

@[expose] public section

open PrimeSpectrum Set TopologicalSpace

universe u v

namespace Algebra

variable {A : Type u} [CommRing A]
variable {ι : Type v} [Finite ι]

/-- Lemma 15.9.3 (Stacks `07LZ`): a finite pairwise disjoint open cover of `Spec(A ⧸ I)` lifts
to such a cover after an etale base change inducing an equivalence on the closed fiber. -/
@[stacks 07LZ]
theorem exists_etale_lift_of_finite_disjoint_open_cover_of_spec_quotient
    (I : Ideal A) (Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))) (hCover : IsOpenCover Ubar)
    (hDisjoint : Pairwise fun i j ↦
      Disjoint (Ubar i : Set (PrimeSpectrum (A ⧸ I)))
        (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
      (U' : ι → Opens (PrimeSpectrum A')),
        IsOpenCover U' ∧
          (Pairwise fun i j ↦
            Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
          ∀ j,
            comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
              comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                (U' j : Set (PrimeSpectrum A')) := sorry

end Algebra
