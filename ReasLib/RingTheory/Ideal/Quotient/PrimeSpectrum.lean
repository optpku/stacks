/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.Prime
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime spectra of quotient rings

This leaf packages the topological comparison between the prime spectrum of a
quotient ring and the zero locus of its defining ideal.  The range computation
is exposed separately so that downstream constructions can reuse it without
unfolding the homeomorphism.

@stack 00E5
-/

noncomputable section

universe u

namespace Ideal

open PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- The image of the spectrum map induced by `R → R ⧸ I` is exactly the zero
locus of `I`. -/
theorem range_comap_quotientMk (I : Ideal R) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- The quotient map `R → R ⧸ I` induces a homeomorphism from
`PrimeSpectrum (R ⧸ I)` onto the zero locus of `I`. -/
@[stacks 00E5]
def primeSpectrum_quotient_homeomorph_zeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set R) :=
  (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).toIsEmbedding.toHomeomorph
    |>.trans (Homeomorph.setCongr (range_comap_quotientMk I))

/-- The quotient-spectrum homeomorphism acts on points by contraction along
the quotient map. -/
@[simp]
theorem primeSpectrum_quotient_homeomorph_zeroLocus_apply
    (I : Ideal R) (x : PrimeSpectrum (R ⧸ I)) :
    (primeSpectrum_quotient_homeomorph_zeroLocus I x).1 =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) x := rfl

/-- The inverse quotient-spectrum homeomorphism sends a prime containing `I`
to its image in `R ⧸ I`. -/
theorem primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
    (I : Ideal R) (x : PrimeSpectrum.zeroLocus (I : Set R)) :
    ((primeSpectrum_quotient_homeomorph_zeroLocus I).symm x).asIdeal =
      x.1.asIdeal.map (Ideal.Quotient.mk I) := by
  let y := (primeSpectrum_quotient_homeomorph_zeroLocus I).symm x
  have hcomap : PrimeSpectrum.comap (Ideal.Quotient.mk I) y = x.1 := by
    rw [← primeSpectrum_quotient_homeomorph_zeroLocus_apply]
    exact congrArg Subtype.val
      ((primeSpectrum_quotient_homeomorph_zeroLocus I).apply_symm_apply x)
  rw [← hcomap, PrimeSpectrum.comap_asIdeal]
  exact (Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective y.asIdeal).symm

/-- The topological Krull dimension of the zero locus of `I` equals the ring
Krull dimension of the quotient `R ⧸ I`. -/
theorem topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) =
      ringKrullDim (R ⧸ I) := by
  calc
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) =
        topologicalKrullDim (PrimeSpectrum (R ⧸ I)) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (primeSpectrum_quotient_homeomorph_zeroLocus I).symm.isHomeomorph
    _ = ringKrullDim (R ⧸ I) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R ⧸ I)

end Ideal

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- The vanishing ideal of an irreducible component of an affine prime spectrum
is prime. -/
theorem vanishingIdeal_irreducibleComponent_isPrime
    (Z : irreducibleComponents (PrimeSpectrum R)) :
    (vanishingIdeal (Z : Set (PrimeSpectrum R))).IsPrime :=
  isIrreducible_iff_vanishingIdeal_isPrime.mp Z.2.1

namespace IrreducibleComponent

/-- An irreducible component of an affine prime spectrum has the Krull
dimension of the quotient by its vanishing ideal. -/
theorem krullDim_eq_quotient
    (Z : irreducibleComponents (PrimeSpectrum R)) :
    topologicalKrullDim (Z : Set (PrimeSpectrum R)) =
      ringKrullDim (R ⧸ vanishingIdeal (Z : Set (PrimeSpectrum R))) := by
  have hZ : (Z : Set (PrimeSpectrum R)) =
      zeroLocus (vanishingIdeal (Z : Set (PrimeSpectrum R)) : Set R) := by
    rw [zeroLocus_vanishingIdeal_eq_closure]
    exact (isClosed_of_mem_irreducibleComponents
      (Z : Set (PrimeSpectrum R)) Z.2).closure_eq.symm
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum R)) =
        topologicalKrullDim
          (zeroLocus (vanishingIdeal (Z : Set (PrimeSpectrum R)) : Set R)) :=
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.setCongr hZ).isHomeomorph
    _ = ringKrullDim (R ⧸ vanishingIdeal (Z : Set (PrimeSpectrum R))) :=
      Ideal.topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient _

end IrreducibleComponent

end PrimeSpectrum
