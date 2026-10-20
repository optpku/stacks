/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.ClosedSeparation
import StacksCheckRecall

/-!
Lemma 15.9.8 (07M3): disjoint closed subsets yield an element equal to `1` modulo one ideal
and landing in the other ideal after applying the ring map.

@stack 07M3
-/

@[expose] public section

universe u v

open Topology PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (φ : R →+* S) (I : Ideal R) (J : Ideal S)
variable (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I)))

/- Lemma 15.9.8 (07M3), in the canonical prime-spectrum notation. -/
@[stacks 07M3]
#check
  (exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
      φ I J hdisj :
    ∃ r : R, Ideal.Quotient.mk I r = 1 ∧ φ r ∈ J)

#check @sup_comap_eq_top_of_disjoint_closure_image_zeroLocus

end
