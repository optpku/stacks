/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Opens

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a Noetherian ring `R`, every coherent module on a principal open subscheme
of `Spec R` is isomorphic to the restriction of a coherent module on `Spec R`. -/
theorem exists_isCoherent_restrict_basicOpen {R : CommRingCat.{u}} [IsNoetherianRing R] (f : R)
    (𝒢 : ((Spec R).basicOpen ((ΓSpecIso R).inv f)).toScheme.Modules) [𝒢.IsCoherent] :
    ∃ ℱ : (Spec R).Modules, ℱ.IsCoherent ∧
      Nonempty (ℱ.restrict (((Spec R).basicOpen ((ΓSpecIso R).inv f)).ι) ≅ 𝒢) := sorry

end AlgebraicGeometry.Scheme.Modules
