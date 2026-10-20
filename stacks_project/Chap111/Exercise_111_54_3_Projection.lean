/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Projection
public import stacks_project.Chap111.Exercise_111_54_3_Hypersurface

/-!
# Coordinate projection of a plane curve

The canonical projection and polar derivative are supplied by the shared
plane-curve projection API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.projection :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d),
    centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base →
      (Hypersurface.scheme 2 d F hF ⟶ ProjectiveSpace.scheme k 1))

#check (MvPolynomial.IsHomogeneous.pderiv (i := (2 : Fin 3)) hF :
  ramificationEquation F ∈ ProjectiveSpace.grading k 2 (d - 1))

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
