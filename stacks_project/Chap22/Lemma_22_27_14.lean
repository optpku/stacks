/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Pretriangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable (B : CompBoundaryAssignment R A) (C : B.AdmissibleCones)
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]
variable [Limits.HasZeroObject (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]

/- Lemma 22.27.14 (09QW): the triangles in `K R A` isomorphic to triangles supplied by the
explicit admissible-cone family `C` form a pretriangulation. -/
@[stacks 09QW]
#check (pretriangulated C : Pretriangulated (K R A))

#check (C.distinguishedTrianglesInK : Set (Triangle (K R A)))
#check (distinguishedTrianglesInK.cone_mem C :
  ∀ {x y : Comp R A} (f : x ⟶ y), (C.cone f).triangleInK ∈ C.distinguishedTrianglesInK)
