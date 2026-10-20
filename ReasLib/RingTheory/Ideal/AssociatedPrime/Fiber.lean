module

public import Mathlib.RingTheory.TensorProduct.Finite
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import ReasLib.RingTheory.RingHom.Fiber.FiniteType

@[expose] public section

/-!
# Exact Associated Primes of Fiber Modules

This file contains an avoidance result for exact associated primes after passing to a
residue-field fiber.
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace associatedPrimesOfModule.Fiber

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N]
variable [Algebra.FiniteType R S] [Module.Finite S N]

/-- If `q : PrimeSpectrum S` lies over `p : PrimeSpectrum R`, then some element outside `q`
maps into every exact associated prime of the fiber module `(p.asIdeal.Fiber S) ⊗[S] N`
that is not contained in the extension of `q`. -/
theorem exists_avoiding (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∀ r ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
          ((p.asIdeal.Fiber S) ⊗[S] N),
        ¬ r ≤ Ideal.map (algebraMap S (p.asIdeal.Fiber S)) q.asIdeal →
          algebraMap S (p.asIdeal.Fiber S) g ∈ r := sorry

end associatedPrimesOfModule.Fiber
