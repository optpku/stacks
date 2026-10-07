module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Octahedron
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The triangulation determined by admissible cones

An explicit admissible-cone family yields the octahedra required by `IsTriangulated` once its
triangles are known to be distinguished in an explicit Mathlib pretriangulation. Specializing to
the pretriangulation constructed from the family gives the canonical Chapter 22 result.
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]
variable [Limits.HasZeroObject (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]

namespace CompBoundaryAssignment.AdmissibleCones

/-- An explicit admissible-cone family whose triangles are distinguished in `P` makes `P`
triangulated. -/
theorem isTriangulated (C : B.AdmissibleCones) (P : Pretriangulated (K R A))
    (hC : C.TrianglesDistinguished P) :
    @IsTriangulated (K R A) _ _ _ _ _ P := sorry

/-- Proposition 22.27.16 (09QY): the pretriangulation of `K R A` constructed from the explicit
admissible-cone family `C` is triangulated. -/
@[stacks 09QY]
theorem isTriangulatedInK (C : B.AdmissibleCones) :
    @IsTriangulated (K R A) _ _ _ _ _ C.pretriangulated := sorry

end CompBoundaryAssignment.AdmissibleCones

end DifferentialGradedCategory

open DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones
