/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Octahedra of admissible-cone triangles

The API accepts an explicit admissible-cone family and an explicit Mathlib pretriangulation.
It also exposes the canonical specialization to the pretriangulation constructed from that family.
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

/-- The octahedron type associated to the cone triangles of two composable maps and their
composite in the explicit pretriangulation `P`. -/
abbrev ConeOctahedron (C : B.AdmissibleCones) (P : Pretriangulated (K R A))
    {x y z : Comp R A} (alpha : x ⟶ y) (beta : y ⟶ z)
    (h_alpha : (C.cone alpha).triangleInK ∈ P.distinguishedTriangles)
    (h_beta : (C.cone beta).triangleInK ∈ P.distinguishedTriangles)
    (h_comp : (C.cone (alpha ≫ beta)).triangleInK ∈ P.distinguishedTriangles) :=
  @Octahedron (K R A) _ _ _ _ _ P
    _ _ _ _ _ _ _ _ _ (Comp.inKFunctor.map_comp alpha beta).symm
    _ _ h_alpha _ _ h_beta _ _ h_comp

/-- The three cone triangles of two composable maps and their composite admit an octahedron in
any explicit pretriangulation in which they are distinguished. -/
theorem nonemptyOctahedron (C : B.AdmissibleCones) (P : Pretriangulated (K R A))
    {x y z : Comp R A} (alpha : x ⟶ y) (beta : y ⟶ z)
    (h_alpha : (C.cone alpha).triangleInK ∈ P.distinguishedTriangles)
    (h_beta : (C.cone beta).triangleInK ∈ P.distinguishedTriangles)
    (h_comp : (C.cone (alpha ≫ beta)).triangleInK ∈ P.distinguishedTriangles) :
    Nonempty (C.ConeOctahedron P alpha beta h_alpha h_beta h_comp) := sorry

/-- The canonical octahedron type for the cone triangles of two composable maps. -/
abbrev ConeOctahedronInK (C : B.AdmissibleCones)
    {x y z : Comp R A} (alpha : x ⟶ y) (beta : y ⟶ z) :=
  C.ConeOctahedron C.pretriangulated alpha beta
    (distinguishedTrianglesInK.cone_mem C alpha)
    (distinguishedTrianglesInK.cone_mem C beta)
    (distinguishedTrianglesInK.cone_mem C (alpha ≫ beta))

/-- Lemma 22.27.15 (09QX): the canonical cone triangles of two composable maps and their
composite admit an octahedron. -/
@[stacks 09QX]
theorem nonemptyConeOctahedronInK (C : B.AdmissibleCones)
    {x y z : Comp R A} (alpha : x ⟶ y) (beta : y ⟶ z) :
    Nonempty (C.ConeOctahedronInK alpha beta) := sorry

end CompBoundaryAssignment.AdmissibleCones

end DifferentialGradedCategory

open DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones
