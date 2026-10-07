module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functoriality of admissible cones up to homotopy

A homotopy-commutative square has a map between any two displayed admissible cones.  The
construction-level API records strict compatibility with the cone legs; the triangle-level API
packages the resulting morphism in the DG homotopy category.
-/

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}

/-- A homotopy-commutative square admits a cone map strictly compatible with both cone legs. -/
theorem exists_map_of_homotopic
    {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂}
    (comm : Homotopic x₁.obj y₂.obj (f₁ ≫ b) (a ≫ f₂)) :
    ∃ c : C₁.obj ⟶ C₂.obj,
      CommSq C₁.toCone b c C₂.toCone ∧
        CommSq C₁.toShift c (a⟦(1 : ℤ)⟧') C₂.toShift := sorry

variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]

/-- Lemma 22.27.3 (09P7): a homotopy-commutative square extends to a morphism of the
associated admissible-cone triangles in `K R A`. -/
@[stacks 09P7]
theorem exists_homInK_of_homotopic
    {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂}
    (comm : Homotopic x₁.obj y₂.obj (f₁ ≫ b) (a ≫ f₂)) :
    ∃ (c : C₁.obj ⟶ C₂.obj) (φ : C₁.triangleInK ⟶ C₂.triangleInK),
      φ.hom₁ = a.inK ∧ φ.hom₂ = b.inK ∧ φ.hom₃ = c.inK := sorry

end DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone
