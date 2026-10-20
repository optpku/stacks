/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
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

/- Proposition 22.27.16 (09QY): the pretriangulation of `K R A` constructed from the explicit
admissible-cone family `C` satisfies the octahedron axiom and is therefore triangulated. -/
@[stacks 09QY]
#check isTriangulatedInK C

#check isTriangulated C C.pretriangulated C.trianglesDistinguishedInK
