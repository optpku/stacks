/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPower.Multi
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.RelativeEulerCharacteristic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.RingTheory.MvPolynomial.Numerical

/-!
# Euler characteristics of finite families of tensor twists

Integral multi-twists of coherent modules on proper algebraic spaces over fields
have numerical-polynomial Euler characteristics bounded in degree by support dimension.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The Euler characteristic of integral multi-twists of a coherent module by a finite
family of invertible modules on an algebraic space proper over a field is a numerical
polynomial of total degree at most the dimension of its scheme-theoretic support. -/
theorem eulerCharacteristic_multiTwist_isMvNumericalPolynomialOfTotalDegreeLE
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [IsLocallyNoetherian X]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)] :
    IsMvNumericalPolynomialOfTotalDegreeLE
      (fun n ↦ eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X)
        (multiTwist F L n))
      (dimension (schemeTheoreticSupport F).X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
