/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.MultiTwist
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

/-!
# Top-dimensional component contributions to Euler characteristics

This file records the difference between the Euler characteristic of a twisted coherent module
and the stalk-length-weighted Euler characteristics of its top-dimensional support components.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
variable (ℱ : X.Modules) [ℱ.IsCoherent]
variable {r : ℕ} (L : Fin r → X.Modules) [∀ j : Fin r, Invertible (L j)]

/-- The difference between the Euler characteristic of a finite tensor twist of a coherent module
and the multiplicity-weighted Euler characteristics of the corresponding twists on a finite
family of closed subschemes. -/
def eulerCharacteristicMultiTwistSubTopDimComponentSum
    {ι : Type v} [Fintype ι]
    (Z : ι → X.IdealSheafData) (m : ι → ℕ) :
    (Fin r → ℤ) → ℤ :=
  fun n ↦
    Scheme.Hom.eulerCharacteristic f (TensorPower.multiTwist ℱ L n) -
      ∑ i : ι,
        (m i : ℤ) * Intersection.eulerCharacteristic k f (Z i) L n

/-- Evaluation of the top-dimensional component deviation unfolds to its defining difference of
Euler characteristics. -/
theorem eulerCharacteristicMultiTwistSubTopDimComponentSum_def
    {ι : Type v} [Fintype ι]
    (Z : ι → X.IdealSheafData) (m : ι → ℕ) (n : Fin r → ℤ) :
    eulerCharacteristicMultiTwistSubTopDimComponentSum f ℱ L Z m n =
      Scheme.Hom.eulerCharacteristic f (TensorPower.multiTwist ℱ L n) -
        ∑ i : ι,
          (m i : ℤ) * Intersection.eulerCharacteristic k f (Z i) L n := sorry

/-- For a coherent module on a scheme proper over a field, its finite-twist Euler-characteristic
deviation from the stalk-length-weighted contributions of all maximal-dimensional support
components is represented by a rational multivariable polynomial which is zero or has total
degree strictly below the dimension of the support. -/
theorem eulerCharacteristic_multiTwist_sub_topDimComponentSum_hasLowerDegree
    {ι : Type v} [Fintype ι]
    (ξ : ι → X) (Z : ι → X.IdealSheafData)
    (h_integral : ∀ i, IsIntegral (Z i).subscheme)
    (h_component_mem :
      ∀ i, ξ i ∈ X.minimalSpecializationPoints (RingedSpace.moduleSupport ℱ))
    (h_component_generic :
      ∀ i, IsGenericPoint (ξ i) ((Z i).support : Set X))
    (h_component_topDim :
      ∀ i,
        topologicalKrullDim (Z i).subscheme =
          topologicalKrullDim (RingedSpace.moduleSupport ℱ))
    (h_exhaustive :
      ∀ x : X,
        x ∈ X.minimalSpecializationPoints (RingedSpace.moduleSupport ℱ) →
          topologicalKrullDim (closure ({x} : Set X)) =
            topologicalKrullDim (RingedSpace.moduleSupport ℱ) →
            ∃ i, ξ i = x)
    (h_injective : Function.Injective ξ)
    (m : ι → ℕ)
    (h_length :
      ∀ i,
        Module.length (X.presheaf.stalk (ξ i)) (RingedSpace.stalkModuleCat ℱ (ξ i)) = m i) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨
        P.totalDegreeWithBotENat <
          topologicalKrullDim (RingedSpace.moduleSupport ℱ)) ∧
        ∀ n : Fin r → ℤ,
          MvPolynomial.eval (fun j : Fin r ↦ (n j : ℚ)) P =
            (eulerCharacteristicMultiTwistSubTopDimComponentSum f ℱ L Z m n : ℚ) := sorry

end AlgebraicGeometry.Scheme.Modules
