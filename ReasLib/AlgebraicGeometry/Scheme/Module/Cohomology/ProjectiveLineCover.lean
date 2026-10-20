/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A scheme over a field covered by two opens isomorphic over the base to the projective
line, whose intersection is isomorphic over the base to the affine line, has
infinite-dimensional first cohomology of its structure sheaf. -/
theorem cohomology_one_not_finiteDimensional {k : Type u} [Field k]
    (X : SchemeOverField k)
    (X₁ X₂ : X.left.Opens) (hcover : X₁ ⊔ X₂ = ⊤)
    (hX₁ : IsIsomorphic (Over.mk (X₁.ι ≫ X.hom)) (ProjectiveSpace.schemeOver k 1))
    (hX₂ : IsIsomorphic (Over.mk (X₂.ι ≫ X.hom)) (ProjectiveSpace.schemeOver k 1))
    (hX₁₂ : IsIsomorphic (Over.mk ((X₁ ⊓ X₂).ι ≫ X.hom))
      (Over.mk (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))) :
    ¬ FiniteDimensional k
        (Scheme.Hom.cohomology X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1) := sorry

end AlgebraicGeometry.SchemeOverField
