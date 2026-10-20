/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- An open immersion between quasi-affine schemes is the pullback of the induced morphism
between their spectra of global sections along their canonical morphisms to those spectra. -/
theorem isPullback_toSpecΓ_toSpecΓ_of_isOpenImmersion
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    [U.IsQuasiAffine] [V.IsQuasiAffine] :
    IsPullback j U.toSpecΓ V.toSpecΓ (Spec.map j.appTop) := sorry

end AlgebraicGeometry.Scheme
