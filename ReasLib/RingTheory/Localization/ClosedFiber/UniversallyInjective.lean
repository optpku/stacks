/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.MkLinearMap
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.Localization.ClosedFiber

/-!
# Universal injectivity from regular elements of a closed fiber

This file gives projective and essential-finite-presentation/flatness criteria for universal
injectivity of the regular elements of a closed fiber and of the resulting localization map.
-/

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

section Projective

variable [Module.Projective R N]

/-- Every element acting regularly on the closed fiber of a projective module acts on the
module by a universally injective linear map over the local base ring. -/
@[stacks 05FR]
theorem universallyInjective_smul_of_projective
    (s : nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N)))) :
    LinearMap.UniversallyInjective.{u, w, w, z}
      (DistribSMul.toLinearMap R N (s : S)) := sorry

/-- The canonical map from a projective module to its localization at the elements acting
regularly on its closed fiber is universally injective over the local base ring. -/
@[stacks 05FR]
theorem universallyInjective_mkLinearMap_of_projective :
    LinearMap.UniversallyInjective.{u, w, max v w, z}
      ((LocalizedModule.mkLinearMap
        (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N)))) N).restrictScalars R) := sorry

end Projective

section EssentiallyFinitePresentation

variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [Module.FinitePresentation S N] [Module.Flat R N]

/-- Every element acting regularly on the closed fiber of a finitely presented module that is
flat over the local base ring acts by a universally injective linear map over that base ring. -/
@[stacks 05DF]
theorem universallyInjective_smul
    (hess : RingHom.EssFinitePresentation (algebraMap R S))
    (s : nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N)))) :
    LinearMap.UniversallyInjective.{u, w, w, z}
      (DistribSMul.toLinearMap R N (s : S)) := sorry

/-- The canonical map from a finitely presented module that is flat over a local base ring to its
localization at the elements acting regularly on its closed fiber is universally injective. -/
@[stacks 05DF]
theorem universallyInjective_mkLinearMap
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) :
    LinearMap.UniversallyInjective.{u, w, max v w, z}
      ((LocalizedModule.mkLinearMap
        (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N)))) N).restrictScalars R) := sorry

end EssentiallyFinitePresentation

end Module.ClosedFiberLocalization
