/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus.Closed
import StacksCheckRecall

/-!
15.19.1.1 (05LQ): the flatness condition on every prime of
`V(I'.map (algebraMap R' S') + J')` is the corresponding closed-subset inclusion in the
flat-over-base locus.

@stack 05LQ
-/

@[expose] public section

open Ideal PrimeSpectrum

universe u v w

variable {R' : Type u} {S' : Type v} {M' : Type w}
variable [CommRing R'] [CommRing S'] [Algebra R' S']
variable [AddCommGroup M'] [Module S' M'] [Module R' M'] [IsScalarTower R' S' M']
variable (I' : Ideal R') (J' : Ideal S')

local notation "K'" => I'.map (algebraMap R' S') + J'

/- 15.19.1.1 (05LQ): primewise flatness on `V(I'S' + J')`. -/
@[stacks 05LQ]
#check
  (zeroLocus_subset_flatOverBaseLocus_iff K' :
    zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M' ↔
      ∀ q' : PrimeSpectrum S', q' ∈ zeroLocus (K' : Set S') →
        Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M'))

/- Canonical locus form of the same source condition. -/
#check zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M'
