/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AffineFamilyOver

variable {T : Scheme.{u}} [IsAffine T]

/-- A finite affine family is an h covering exactly when its maps are of finite
presentation and the family admits a refinement by a standard ph covering. -/
theorem hCovering_iff_exists_standardPhRefinement (family : AffineFamilyOver T) :
    Scheme.HCovering (fun i : Fin family.n ↦ Over.mk (family.map i)) ↔
      (∀ i, Scheme.Hom.FinitePresentation (family.map i)) ∧
        ∃ cover : StandardPhCovering T,
          Nonempty (Refinement cover.toAffineFamily family) := sorry

/-- A finite affine family is an h covering exactly when its maps are of finite
presentation and the family is a V covering. -/
theorem hCovering_iff_isVCovering (family : AffineFamilyOver T) :
    Scheme.HCovering (fun i : Fin family.n ↦ Over.mk (family.map i)) ↔
      (∀ i, Scheme.Hom.FinitePresentation (family.map i)) ∧
        IsVCovering T family.U family.map := sorry

end AlgebraicGeometry.AffineFamilyOver
