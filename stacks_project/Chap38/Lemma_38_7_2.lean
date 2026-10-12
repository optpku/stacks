/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.ClosedFiber.UniversallyInjective
import StacksCheckRecall

@[expose] public section

universe u v w z

namespace Module.ClosedFiberLocalization

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
variable [Module.Finite
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
  (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
    (⊤ : Submodule S N)))]
variable [Module.FinitePresentation S N] [Module.Flat R N]

/- Lemma 38.7.2 (1): every element acting regularly on the closed fiber of `N`
acts on `N` by a universally injective `R`-linear map. -/
@[stacks 05DF] #check
  (Module.ClosedFiberLocalization.universallyInjective_smul :
    ∀ (hess : RingHom.EssFinitePresentation (algebraMap R S))
      (s : nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N)))),
      LinearMap.UniversallyInjective.{u, w, w, z}
        (DistribSMul.toLinearMap R N (s : S)))

/- Lemma 38.7.2 (2): localization of `N` at the elements acting regularly on
its closed fiber is universally injective over `R`. -/
@[stacks 05DF] #check
  (Module.ClosedFiberLocalization.universallyInjective_mkLinearMap :
    ∀ (hess : RingHom.EssFinitePresentation (algebraMap R S)),
      LinearMap.UniversallyInjective.{u, w, max v w, z}
        ((LocalizedModule.mkLinearMap
          (nonZeroSMulDivisors S
            (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
              (⊤ : Submodule S N)))) N).restrictScalars R))

end Module.ClosedFiberLocalization
