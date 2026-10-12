/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Support
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Domain
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Serre
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion-free finite modules and associated primes

This leaf packages the standard characterizations of a nonzero finite torsion-free module over a
Noetherian domain in terms of finite free embeddings, associated primes, support, Serre's
condition `(S_1)`, and embedded associated primes.
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Module.IsTorsionFree

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/-- For a nonzero finite module over a Noetherian domain, torsion-freeness, embeddability in a
finite free module, the singleton associated-prime condition, and the corresponding support and
Serre conditions are equivalent. -/
@[stacks 0AUV "torsion-free finite modules and associated primes"]
theorem tfae_associatedPrimes_support_serreS1 :
    List.TFAE
      [ IsTorsionFree R M,
        ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f,
        associatedPrimes R M = {⊥},
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1,
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ] := sorry

end Module.IsTorsionFree
