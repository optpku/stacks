/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.QuasiAffine

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The source of an integral morphism to a quasi-affine scheme is quasi-affine. -/
theorem IsQuasiAffine.of_isIntegralHom {U X : Scheme.{u}} (f : U ⟶ X)
    [X.IsQuasiAffine] [IsIntegralHom f] : U.IsQuasiAffine := sorry

/-- For an integral morphism to a quasi-affine scheme, the square formed by the morphism,
the canonical morphisms to the spectra of global sections, and the induced map of spectra
is cartesian. -/
theorem isPullback_toSpecΓ_of_isIntegralHom {U X : Scheme.{u}} (f : U ⟶ X)
    [X.IsQuasiAffine] [IsIntegralHom f] :
    IsPullback f U.toSpecΓ X.toSpecΓ (Spec.map f.appTop) := sorry

end AlgebraicGeometry.Scheme
