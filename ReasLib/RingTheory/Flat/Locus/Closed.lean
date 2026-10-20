/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Locus

/-!
# Closed subsets of flatness loci

Containment of a Zariski closed subset in a flatness locus and the corresponding pointwise
flatness condition.
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace Ideal

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The closed subset `V(K)` lies in the flat-over-`R` locus of `M` exactly when every prime
of `S` containing `K` has an `R`-flat localization of `M`. -/
@[stacks 052W, stacks 05LQ "closed subsets of the flatness locus"]
theorem zeroLocus_subset_flatOverBaseLocus_iff (K : Ideal S) :
    zeroLocus (K : Set S) ⊆ Module.flatOverBaseLocus R S M ↔
      ∀ q : PrimeSpectrum S,
        q ∈ zeroLocus (K : Set S) →
          Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

end Ideal
