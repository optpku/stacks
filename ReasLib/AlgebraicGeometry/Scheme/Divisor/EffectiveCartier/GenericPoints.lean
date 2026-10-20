/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints

/-!
# Generic points and effective Cartier divisors

An effective Cartier divisor contains no generic point of an irreducible component of its
ambient scheme.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsEffectiveCartierDivisor

/-- The generic points of the irreducible components of a scheme lie outside the support of
every effective Cartier divisor. -/
theorem genericPoints_subset_compl_support {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    genericPoints X ⊆ (D.support : Set X)ᶜ := sorry

end AlgebraicGeometry.IsEffectiveCartierDivisor
