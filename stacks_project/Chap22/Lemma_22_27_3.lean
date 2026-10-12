/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Functoriality
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]
variable {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
variable (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
variable {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂}
variable (comm : Homotopic x₁.obj y₂.obj (f₁ ≫ b) (a ≫ f₂))

/- Lemma 22.27.3 (09P7): a homotopy-commutative square extends to a morphism between the
associated admissible-cone triangles in the DG homotopy category. -/
@[stacks 09P7] #check
  (DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone.exists_homInK_of_homotopic
      C₁ C₂ comm :
    ∃ (c : C₁.obj ⟶ C₂.obj) (φ : C₁.triangleInK ⟶ C₂.triangleInK),
      φ.hom₁ = a.inK ∧ φ.hom₂ = b.inK ∧ φ.hom₃ = c.inK)

/- The construction-level API retains the explicit closed map between the two cone objects. -/
#check
  @DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone.exists_map_of_homotopic
