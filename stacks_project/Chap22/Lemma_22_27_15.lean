/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Octahedron
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
variable {x y z : Comp R A} (alpha : x ⟶ y) (beta : y ⟶ z)

/- Lemma 22.27.15 (09QX): the explicit cone triangles of `alpha`, `beta`, and `alpha ≫ beta`
admit an octahedron in the pretriangulation constructed from `C`. -/
@[stacks 09QX]
#check (nonemptyConeOctahedronInK C alpha beta :
  Nonempty (C.ConeOctahedronInK alpha beta))
