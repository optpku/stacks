/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Zero loci of ideals

This file records the intersection formula for zero loci in the orientation used for
successive support conditions, together with the criterion for two zero loci to be disjoint.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The intersection of the zero loci of two finitely generated ideals is the zero locus of
their supremum. -/
theorem zeroLocus_inter_of_fg (I J : Ideal A) (hI : I.FG) (hJ : J.FG) :
    zeroLocus I ∩ zeroLocus J = zeroLocus ((I ⊔ J : Ideal A) : Set A) := sorry

end PrimeSpectrum

namespace PrimeSpectrum

/-- Two ideal zero loci in the prime spectrum are disjoint exactly when the ideals generate the
unit ideal. -/
theorem disjoint_zeroLocus_iff {R : Type u} [CommSemiring R] (I J : Ideal R) :
    Disjoint (zeroLocus (I : Set R)) (zeroLocus (J : Set R)) ↔ I ⊔ J = ⊤ := sorry

end PrimeSpectrum
