/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.Components

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u v

/- Lemma 33.45.2: for a coherent module on a scheme proper over a field, subtracting the
stalk-length-weighted Euler characteristics of the twists on all maximal-dimensional support
components from the Euler characteristic of each twist gives a rational multivariable polynomial
which is zero or has total degree strictly below the dimension of the support. -/
@[stacks 0BEN] #check
  (AlgebraicGeometry.Scheme.Modules.eulerCharacteristic_multiTwist_sub_topDimComponentSum_hasLowerDegree :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      {r : ℕ} (L : Fin r → X.Modules)
      [∀ j : Fin r, Scheme.Modules.Invertible (L j)]
      {ι : Type v} [Fintype ι]
      (ξ : ι → X) (Z : ι → X.IdealSheafData),
      (∀ i, IsIntegral (Z i).subscheme) →
        (∀ i, ξ i ∈ X.minimalSpecializationPoints (RingedSpace.moduleSupport ℱ)) →
          (∀ i, IsGenericPoint (ξ i) ((Z i).support : Set X)) →
            (∀ i,
              topologicalKrullDim (Z i).subscheme =
                topologicalKrullDim (RingedSpace.moduleSupport ℱ)) →
              (∀ x : X,
                x ∈ X.minimalSpecializationPoints (RingedSpace.moduleSupport ℱ) →
                  topologicalKrullDim (closure ({x} : Set X)) =
                    topologicalKrullDim (RingedSpace.moduleSupport ℱ) →
                      ∃ i, ξ i = x) →
                Function.Injective ξ →
                  ∀ (m : ι → ℕ),
                    (∀ i,
                      Module.length (X.presheaf.stalk (ξ i))
                        (RingedSpace.stalkModuleCat ℱ (ξ i)) = m i) →
                      ∃ P : MvPolynomial (Fin r) ℚ,
                        (P = 0 ∨
                          P.totalDegreeWithBotENat <
                            topologicalKrullDim (RingedSpace.moduleSupport ℱ)) ∧
                          ∀ n : Fin r → ℤ,
                            MvPolynomial.eval (fun j : Fin r ↦ (n j : ℚ)) P =
                              (AlgebraicGeometry.Scheme.Modules.eulerCharacteristicMultiTwistSubTopDimComponentSum
                                f ℱ L Z m n : ℚ))
