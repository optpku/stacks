/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower.Multi
public import ReasLib.RingTheory.MvPolynomial.Numerical

/-!
# Euler characteristics of finite families of tensor twists

This file relates the Euler characteristic of integral tensor twists of a coherent scheme module
to multivariable numerical polynomials.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
variable (ℱ : X.Modules) [ℱ.IsCoherent]
variable {r : ℕ} (L : Fin r → X.Modules) [∀ j : Fin r, Invertible (L j)]

/-- The Euler characteristic of all integral twists of a coherent module by a finite family of
invertible modules is represented on integer exponent vectors by a rational multivariate
polynomial whose total degree is at most the dimension of the module's support. -/
theorem eulerCharacteristic_multiTwist_isMvNumericalPolynomialOfTotalDegreeLE :
    IsMvNumericalPolynomialOfTotalDegreeLE
      (fun n ↦ Scheme.Hom.eulerCharacteristic f (TensorPower.multiTwist ℱ L n))
      (topologicalKrullDim (moduleSupport ℱ)) := sorry

end AlgebraicGeometry.Scheme.Modules
