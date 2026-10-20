module

public import ReasLib.RingTheory.Localization.ClosedFiber.UniversallyInjective
import StacksCheckRecall

@[expose] public section

universe u v w z

namespace Module.ClosedFiberLocalization

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [IsNoetherianRing
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
variable [Module.Finite
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
  (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
    (⊤ : Submodule S N)))]
variable [Module.Projective R N]

/- Lemma 38.7.6 (1): every element acting regularly on the closed fiber of a
projective `R`-module `N` acts on `N` by a universally injective `R`-linear map. -/
@[stacks 05FR] #check
  (Module.ClosedFiberLocalization.universallyInjective_smul_of_projective :
    ∀ s : nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N))),
      LinearMap.UniversallyInjective.{u, w, w, z}
        (DistribSMul.toLinearMap R N (s : S)))

/- Lemma 38.7.6 (2): the canonical map from a projective `R`-module `N` to
its localization at the elements acting regularly on its closed fiber is
universally injective over `R`. -/
@[stacks 05FR] #check
  (Module.ClosedFiberLocalization.universallyInjective_mkLinearMap_of_projective :
    LinearMap.UniversallyInjective.{u, w, max v w, z}
      ((LocalizedModule.mkLinearMap
        (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N)))) N).restrictScalars R))

end Module.ClosedFiberLocalization
