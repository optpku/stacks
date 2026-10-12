/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative.UniversallyInjective
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w x z

namespace relativeAssassin

variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S N]
variable [Module.Flat R N] [Module.Flat S S']

/- Lemma 38.7.4: coverage of the relative associated primes by the image of
`Spec(S') → Spec(S)` makes the canonical map `N → S' ⊗[S] N` universally
injective over `R`. -/
@[stacks 05DH] #check
  (relativeAssassin.universallyInjective_baseChange :
    ∀ (h_range : relativeAssassin R S N ⊆
      Set.range (PrimeSpectrum.comap (algebraMap S S'))),
      LinearMap.UniversallyInjective.{u, x, max w x, z}
        ((TensorProduct.mk S S' N 1).restrictScalars R))

end relativeAssassin
