/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology

/-!
# Cohomology and finite affine stratifications

The affine stratification number of a nonempty quasi-compact quasi-separated scheme bounds the
degrees in which its quasi-coherent modules can have nonzero cohomology.
-/

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/-- The cohomology of a quasi-coherent module on a nonempty quasi-compact quasi-separated scheme
vanishes in every degree strictly above the scheme's affine stratification number. -/
theorem cohomology_isZero_of_number_lt {X : Scheme.{u}} [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ)
    (hp : number X < p) : IsZero (Scheme.Modules.cohomology ℱ p) := sorry

end AlgebraicGeometry.Scheme.FiniteAffineStratification
