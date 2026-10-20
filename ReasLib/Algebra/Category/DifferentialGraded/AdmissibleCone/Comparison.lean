module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Factorization
public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle

/-!
# Comparison of Admissible Cone Triangles

Admissible short complexes compare to displayed cone triangles by triangle isomorphisms whose
third components are represented by explicit homotopy equivalences in the closed category.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]

/-- Lemma 22.27.11 (09QS): twice rotating the triangle of a graded-split short complex gives
the admissible-cone triangle of its connecting morphism. The third component is represented by
an explicit homotopy equivalence in `Comp R A`. -/
@[stacks 09QS]
theorem exists_rotateRotateIso
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting)
    (C : B.AdmissibleCone (B.boundary σ)) :
    ∃ (e : HomotopyEquiv (S.X₂⟦(1 : ℤ)⟧) C.obj)
      (φ : (B.associatedTriangleInK σ).rotate.rotate ≅ C.triangleInK),
      φ.hom.hom₁ = 𝟙 S.X₃.inK ∧
        φ.hom.hom₂ =
          ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).inv.app S.X₁ ∧
        φ.hom.hom₃ =
          ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).inv.app S.X₂ ≫
            e.hom.inK := sorry

/-- Lemma 22.27.13 (1) (09QU): a graded-split short complex compares to an admissible cone on
its first map by a triangle isomorphism represented on the third object by a homotopy
equivalence. -/
@[stacks 09QU]
theorem exists_triangleIso_toShortComplex
    (S : ShortComplex (Comp R A)) (σ : S.GradedSplitting) (C : B.AdmissibleCone S.f) :
    ∃ (e : HomotopyEquiv C.obj S.X₃)
      (φ : C.triangleInK ≅ B.associatedTriangleInK σ),
      φ.hom.hom₁ = 𝟙 S.X₁.inK ∧
        φ.hom.hom₂ = 𝟙 S.X₂.inK ∧ φ.hom.hom₃ = e.hom.inK := sorry

/-- Lemma 22.27.13 (2) (09QU): a factorization through an admissibly monic map and a homotopy
retract compares its graded-split short complex to the admissible cone of the original map by a
triangle isomorphism. -/
@[stacks 09QU]
theorem exists_triangleIso_fromFactorization
    (S : ShortComplex (Comp R A)) (σ : S.GradedSplitting)
    {y : Comp R A} {f : S.X₁ ⟶ y} (r : HomotopyRetract S.X₂ y)
    (hfactor : S.f ≫ r.projection = f) (C : B.AdmissibleCone f) :
    ∃ (e : HomotopyEquiv S.X₃ C.obj)
      (φ : B.associatedTriangleInK σ ≅ C.triangleInK),
      φ.hom.hom₁ = 𝟙 S.X₁.inK ∧
        φ.hom.hom₂ = r.projection.inK ∧ φ.hom.hom₃ = e.hom.inK := sorry

end DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone
