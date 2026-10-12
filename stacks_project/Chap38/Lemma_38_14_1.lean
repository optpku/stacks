/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative.ClosedFiber
import StacksCheckRecall

@[expose] public section

universe u v w

namespace relativeAssassin

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Projective R N]
variable [IsNoetherianRing
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
variable [Module.Finite
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
  (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
    (⊤ : Submodule S N)))]

/- Lemma 38.14.1: if `N` is projective over the local ring `R` and its closed
fiber is finite over the Noetherian closed-fiber ring, every prime in the
relative assassin of `N` remains proper after adjoining the extension of the
maximal ideal of `R`. -/
@[stacks 05FV] #check
  (relativeAssassin.add_map_maximalIdeal_ne_top :
    ∀ (q : PrimeSpectrum S), q ∈ relativeAssassin R S N →
      q.asIdeal + Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊤)

end relativeAssassin
