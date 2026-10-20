/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Images of Zero Loci

@stack 0H7L
-/

@[expose] public section

open Set Topology

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The image of a zero locus is dense exactly when its contraction is nilpotent. -/
@[stacks 0H7L "density criterion for images of zero loci"]
theorem dense_image_comap_zeroLocus_iff (f : R →+* S) (I : Ideal S) :
    Dense (comap f '' zeroLocus I) ↔ I.comap f ≤ nilradical R := by
  rw [dense_iff_closure_eq, closure_image_comap_zeroLocus,
    zeroLocus_eq_univ_iff]
  exact SetLike.coe_subset_coe

/-- Over a reduced base, density is equivalent to vanishing of the contracted ideal. -/
@[stacks 0H7L "density criterion over a reduced base"]
theorem dense_image_comap_zeroLocus_iff_comap_eq_bot [IsReduced R]
    (f : R →+* S) (I : Ideal S) :
    Dense (comap f '' zeroLocus I) ↔ I.comap f = ⊥ := by
  rw [dense_image_comap_zeroLocus_iff,
    nilradical_eq_bot_iff.mpr (inferInstance : IsReduced R), le_bot_iff]

/-- Over a reduced base, nondensity is equivalent to nonzero contraction. -/
@[stacks 0H7L "nondensity criterion over a reduced base"]
theorem not_dense_image_comap_zeroLocus_iff [IsReduced R]
    (f : R →+* S) (I : Ideal S) :
    ¬ Dense (comap f '' zeroLocus I) ↔ I.comap f ≠ ⊥ :=
  not_congr (dense_image_comap_zeroLocus_iff_comap_eq_bot f I)

/-- Over a reduced base, a zero locus with nonzero contraction has nondense image. -/
@[stacks 0H7L "nondense image of a nonzero contraction"]
theorem not_dense_image_comap_zeroLocus [IsReduced R]
    (f : R →+* S) (I : Ideal S) (hI : I.comap f ≠ ⊥) :
    ¬ Dense (comap f '' zeroLocus I) :=
  (not_dense_image_comap_zeroLocus_iff f I).2 hI

end PrimeSpectrum
