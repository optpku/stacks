/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.UFD
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.StalkCriterion

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- An integral closed subscheme of codimension one is an effective Cartier divisor when the
ambient local rings along its support are unique factorization domains. -/
theorem isEffectiveCartierDivisor_of_uniqueFactorizationMonoid
    (D : X.IdealSheafData) [IsIntegral D.subscheme]
    (hcodim : ringKrullDim (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) = 1)
    (hUFD : ∀ x : X, x ∈ D.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
