/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Cohomology of infinite punctured affine space

This file defines the structure-sheaf cohomology of the complement of the
origin in countably infinite affine space and records its positive-degree
vanishing.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace.Infinite

/-- The structure morphism of the complement of the origin in infinite affine space over `k`. -/
abbrev puncturedToBase (k : Type u) [Field k] :
    (coordinatePuncturedOpen ℕ k).toScheme ⟶ Spec (CommRingCat.of k) :=
  (coordinatePuncturedOpen ℕ k).ι ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* coordinateRing ℕ k))

/-- The structure sheaf of the complement of the origin, as a sheaf of modules. -/
abbrev unitModule (k : Type u) [Field k] :
    (coordinatePuncturedOpen ℕ k).toScheme.Modules :=
  SheafOfModules.unit (coordinatePuncturedOpen ℕ k).toScheme.ringCatSheaf

/-- Zariski cohomology of the structure sheaf on countably infinite punctured affine space, viewed as a `k`-module. -/
abbrev structureSheafCohomology (k : Type u) [Field k] (n : ℕ) : ModuleCat k :=
  Scheme.Hom.cohomology (puncturedToBase k) (unitModule k) n

/-- The structure-sheaf cohomology of countably infinite punctured affine space vanishes in every positive degree. -/
theorem cohomology_isZero (k : Type u) [Field k] (i : ℕ) (hi : 0 < i) :
    IsZero (structureSheafCohomology k i) := sorry

/-- The first cohomology of countably infinite punctured affine space with coefficients in its structure sheaf vanishes. -/
theorem cohomology_one_isZero (k : Type u) [Field k] :
    IsZero (structureSheafCohomology k 1) := sorry

end AlgebraicGeometry.PuncturedAffineSpace.Infinite
