/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Comparable
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Incomparability in Fibers of Integral Maps

@stack 00GT
-/

@[expose] public section

universe u v

namespace RingHom.IsIntegral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Strict containment of prime ideals remains strict after contraction along an integral map. -/
@[stacks 00GT "strict contraction along an integral map"]
theorem comap_lt_comap (hf : f.IsIntegral) {I J : Ideal S} [I.IsPrime]
    (hIJ : I < J) : I.comap f < J.comap f := by
  obtain ⟨hIJ, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp hIJ
  obtain ⟨p, hp, hpx⟩ := hf x
  exact Ideal.comap_lt_comap_of_root_mem_sdiff hIJ ⟨hxJ, hxI⟩
    (Polynomial.map_monic_ne_zero hp) (hpx.symm ▸ I.zero_mem)

/-- Distinct prime ideals with the same contraction along an integral map are incomparable. -/
@[stacks 00GT "incomparability of prime ideals under an integral map"]
theorem incompRel_of_comap_eq (hf : f.IsIntegral)
    {I J : Ideal S} [I.IsPrime] [J.IsPrime]
    (hne : I ≠ J) (hcomap : I.comap f = J.comap f) :
    IncompRel (· ≤ ·) I J := by
  constructor
  · intro hIJ
    exact (hf.comap_lt_comap (lt_of_le_of_ne hIJ hne)).ne hcomap
  · intro hJI
    exact (hf.comap_lt_comap (lt_of_le_of_ne hJI hne.symm)).ne hcomap.symm

end RingHom.IsIntegral

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Distinct points in one fiber of an integral map on spectra are incomparable. -/
@[stacks 00GT "incomparability in a fiber of an integral spectrum map"]
theorem incompRel_of_comap_eq_of_isIntegral
    (hf : f.IsIntegral) {p q : PrimeSpectrum S} (hne : p ≠ q)
    (hcomap : comap f p = comap f q) :
    IncompRel (· ≤ ·) p q := by
  have hne' : p.asIdeal ≠ q.asIdeal := fun h ↦ hne (PrimeSpectrum.ext h)
  have hcomap' : p.asIdeal.comap f = q.asIdeal.comap f := by
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg asIdeal hcomap
  change IncompRel (· ≤ ·) p.asIdeal q.asIdeal
  exact hf.incompRel_of_comap_eq hne' hcomap'

/-- Every fiber of the spectrum map induced by an integral ring homomorphism is an antichain. -/
@[stacks 00GT "fibers of integral spectrum maps are antichains"]
theorem isAntichain_comap_fiber_of_isIntegral
    (hf : f.IsIntegral) (p : PrimeSpectrum R) :
    IsAntichain (· ≤ ·) {q : PrimeSpectrum S | comap f q = p} := by
  intro q hq q' hq' hne hle
  exact (incompRel_of_comap_eq_of_isIntegral hf hne (hq.trans hq'.symm)).1 hle

end PrimeSpectrum
