/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus.Closed
import StacksCheckRecall

/-!
15.18.0.1 (052W): for every prime `q` of `S` in `V(IS)`, the localization `M_q` is flat over
`R`. Equivalently, `V(IS)` is contained in the flat-over-`R` locus of `M`.

@stack 052W
-/

@[expose] public section

open PrimeSpectrum

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (I : Ideal R)

namespace Ideal

/- 15.18.0.1 (052W), specialized to the extension of `I` along `R → S`. -/
@[stacks 052W]
#check
  (zeroLocus_subset_flatOverBaseLocus_iff
      (R := R) (S := S) (M := M) (I.map (algebraMap R S)) :
    zeroLocus (I.map (algebraMap R S) : Set S) ⊆ Module.flatOverBaseLocus R S M ↔
      ∀ q : PrimeSpectrum S,
        q ∈ zeroLocus (I.map (algebraMap R S) : Set S) →
          Module.Flat R (LocalizedModule.AtPrime q.asIdeal M))

end Ideal

end
