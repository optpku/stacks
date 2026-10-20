module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Contractibility of the cone of an identity

The identity cone is contractible in every differential graded category equipped with an
admissible-cone assignment.
-/

open CategoryTheory
open scoped DifferentialGradedCategory

universe u v w

namespace DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}

/-- Lemma 22.27.4 (09QK): the identity of a cone on an identity morphism is homotopic to
zero. -/
@[stacks 09QK]
theorem id_homotopic_zero {x : Comp R A} (C : B.AdmissibleCone (𝟙 x)) :
    Homotopic C.obj.obj C.obj.obj (𝟙 C.obj) 0 := sorry

/-- The identity of an identity cone is the differential of a degree `-1` endomorphism. -/
theorem exists_contractingHomotopy {x : Comp R A} (C : B.AdmissibleCone (𝟙 x)) :
    ∃ h : C.obj.obj ⟶[-1] C.obj.obj, D.id C.obj.obj = D.d (-1) h := sorry

end DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone
