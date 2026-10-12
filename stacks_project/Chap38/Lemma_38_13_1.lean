/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Fiber
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace associatedPrimesOfModule.Fiber

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S N]

/- Lemma 38.13.1: if `q : PrimeSpectrum S` lies over `p : PrimeSpectrum R`, then some
`g : S` outside `q` maps into every exact associated prime of the fiber module
`(p.asIdeal.Fiber S) ⊗[S] N` that is not contained in the extension of `q`. -/
@[stacks 0CU6] #check
  (associatedPrimesOfModule.Fiber.exists_avoiding :
    ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S),
      PrimeSpectrum.comap (algebraMap R S) q = p →
        ∃ g : S, g ∉ q.asIdeal ∧
          ∀ r ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
              ((p.asIdeal.Fiber S) ⊗[S] N),
            ¬ r ≤ Ideal.map (algebraMap S (p.asIdeal.Fiber S)) q.asIdeal →
              algebraMap S (p.asIdeal.Fiber S) g ∈ r)

end associatedPrimesOfModule.Fiber
