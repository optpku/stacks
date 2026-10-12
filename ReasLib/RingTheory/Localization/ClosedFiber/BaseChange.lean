/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.ClosedFiber.UniversallyInjective

/-!
# Universal injectivity after flat base change

This file gives a criterion for universal injectivity of a flat base-change map in terms of the
associated primes of the closed fiber.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x z

namespace Module.ClosedFiberLocalization

/-- Let `R → S` be a local homomorphism of local rings, with `S` essentially of finite
presentation over `R`, and let `N` be a finitely presented `S`-module that is flat over `R`.
If `S → T` is flat and the image of `Spec(T) → Spec(S)` contains every associated prime of
`N / 𝔪_R N` lying over `𝔪_R`, then the canonical map `N → T ⊗[S] N` is universally injective
over `R`. -/
@[stacks 05DG]
theorem universallyInjective_baseChange_of_associatedPrimes
    {R : Type u} {S : Type v} {T : Type w} {N : Type x}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N] [Module.Flat S T]
    (hess : RingHom.EssFinitePresentation (algebraMap R S))
    (h_range :
      {q : PrimeSpectrum S |
        q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R ∧
          q.asIdeal ∈ associatedPrimesOfModule S
            (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
              (⊤ : Submodule S N)))} ⊆
        Set.range (PrimeSpectrum.comap (algebraMap S T))) :
    LinearMap.UniversallyInjective.{u, x, max w x, z}
      ((TensorProduct.mk S T N 1).restrictScalars R) := sorry

end Module.ClosedFiberLocalization
