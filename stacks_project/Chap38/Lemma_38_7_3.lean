/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.ClosedFiber.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w x z

namespace Module.ClosedFiberLocalization

variable {R : Type u} {S : Type v} {T : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.FinitePresentation S N] [Module.Flat R N] [Module.Flat S T]

/- Lemma 38.7.3: under the associated-prime coverage hypothesis for the closed
fiber, flat base change induces an `R`-universally injective map. -/
@[stacks 05DG] #check
  (Module.ClosedFiberLocalization.universallyInjective_baseChange_of_associatedPrimes :
    ∀ (hess : RingHom.EssFinitePresentation (algebraMap R S))
      (h_range :
        {q : PrimeSpectrum S |
          q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R ∧
            q.asIdeal ∈ associatedPrimesOfModule S
              (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
                (⊤ : Submodule S N)))} ⊆
          Set.range (PrimeSpectrum.comap (algebraMap S T))),
      LinearMap.UniversallyInjective.{u, x, max w x, z}
        ((TensorProduct.mk S T N 1).restrictScalars R))

end Module.ClosedFiberLocalization
