/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category

/-!
# Triangles Associated to Admissible DG-Module Sequences

A graded `A`-linear splitting of a short complex of differential graded modules determines an
explicit connecting morphism and hence a triangle.  This file packages that triangle before and
after passage to the intrinsic DG homotopy category, together with the canonical comparison
between two choices of splitting.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.ShortComplex

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A))

/-- The triangle of differential graded modules attached to a chosen graded `A`-linear
splitting. -/
def associatedTriangle (sigma : GradedSplitting S) :
    Triangle (DifferentialGradedModule.{u, w} A) :=
  Triangle.mk S.f S.g sigma.connectingHom

/-- The first object of the associated triangle is the kernel term of the short complex. -/
@[simp]
theorem associatedTriangle_obj₁ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).obj₁ = S.X₁ := sorry

/-- The second object of the associated triangle is the middle term of the short complex. -/
@[simp]
theorem associatedTriangle_obj₂ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).obj₂ = S.X₂ := sorry

/-- The third object of the associated triangle is the quotient term of the short complex. -/
@[simp]
theorem associatedTriangle_obj₃ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).obj₃ = S.X₃ := sorry

/-- The first map of the associated triangle is the first map of the short complex. -/
@[simp]
theorem associatedTriangle_mor₁ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).mor₁ = S.f := sorry

/-- The second map of the associated triangle is the second map of the short complex. -/
@[simp]
theorem associatedTriangle_mor₂ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).mor₂ = S.g := sorry

/-- The third map of the associated triangle is the connecting morphism of the splitting. -/
@[simp]
theorem associatedTriangle_mor₃ (sigma : GradedSplitting S) :
    (associatedTriangle S sigma).mor₃ = sigma.connectingHom := sorry

/-- Equation 22.8.1.1 (09K7): the triangle in the DG homotopy category associated to a graded
`A`-linearly split short complex. -/
@[stacks 09K7 "triangle associated to an admissible DG-module short exact sequence"]
def associatedTriangleK (sigma : GradedSplitting S) :
    Triangle (K R (DifferentialGradedModule.{u, w} A)) :=
  (toK A).mapTriangle.obj (associatedTriangle S sigma)

/-- The first object of the associated homotopy-category triangle is represented by `S.X₁`. -/
@[simp]
theorem associatedTriangleK_obj₁ (sigma : GradedSplitting S) :
    (associatedTriangleK S sigma).obj₁ = (toK A).obj S.X₁ := sorry

/-- The second object of the associated homotopy-category triangle is represented by `S.X₂`. -/
@[simp]
theorem associatedTriangleK_obj₂ (sigma : GradedSplitting S) :
    (associatedTriangleK S sigma).obj₂ = (toK A).obj S.X₂ := sorry

/-- The third object of the associated homotopy-category triangle is represented by `S.X₃`. -/
@[simp]
theorem associatedTriangleK_obj₃ (sigma : GradedSplitting S) :
    (associatedTriangleK S sigma).obj₃ = (toK A).obj S.X₃ := sorry

/-- The third map of the associated homotopy-category triangle is represented by the explicit
connecting DG-module morphism, followed by the canonical shift comparison. -/
@[simp]
theorem associatedTriangleK_mor₃ (sigma : GradedSplitting S) :
    (associatedTriangleK S sigma).mor₃ =
      (toK A).map sigma.connectingHom ≫ ((toK A).commShiftIso (1 : ℤ)).hom.app S.X₁ := sorry

/-- The canonical graded correction from `sigma` to `sigma'` is section for `sigma'` followed by
retraction for `sigma`. -/
def splittingCorrection (sigma sigma' : GradedSplitting S) :
    Graded.Hom S.X₃.toGraded S.X₁.toGraded :=
  sigma'.s ≫ sigma.r

/-- The correction is computed by the chosen graded section and retraction. -/
@[simp]
theorem splittingCorrection_hom (sigma sigma' : GradedSplitting S) (n : ℤ) :
    (splittingCorrection S sigma sigma').hom n =
      (sigma.r.hom n).comp (sigma'.s.hom n) := sorry

/-- The shifted correction satisfies the homotopy equation between the two connecting maps. -/
theorem connectingHomotopy_condition (sigma sigma' : GradedSplitting S) :
    (homToCompHom sigma'.connectingHom).val - (homToCompHom sigma.connectingHom).val =
      gradedHomDifferential (-1) (splittingCorrection S sigma sigma').toShiftHomotopy := sorry

/-- The explicit homotopy between the connecting morphisms obtained from two graded
`A`-linear splittings. -/
def connectingHomotopy (sigma sigma' : GradedSplitting S) :
    Homotopy sigma'.connectingHom sigma.connectingHom where
  hom := (splittingCorrection S sigma sigma').toShiftHomotopy
  condition := connectingHomotopy_condition S sigma sigma'

/-- The homogeneous map underlying the splitting-change homotopy is the shifted canonical
correction. -/
@[simp]
theorem connectingHomotopy_hom (sigma sigma' : GradedSplitting S) :
    (connectingHomotopy S sigma sigma').hom =
      (splittingCorrection S sigma sigma').toShiftHomotopy := sorry

/-- Connecting morphisms obtained from two splittings agree in the DG homotopy category. -/
theorem connectingHom_eq_in_K (sigma sigma' : GradedSplitting S) :
    (toK A).map sigma.connectingHom = (toK A).map sigma'.connectingHom := sorry

/-- Lemma 22.8.1 (09K6): changing the graded `A`-linear splitting gives the canonical
identity-on-vertices isomorphism of associated triangles in the DG homotopy category. -/
@[stacks 09K6 "independence of the splitting for an associated DG-module triangle"]
def associatedTriangleIso (sigma sigma' : GradedSplitting S) :
    associatedTriangleK S sigma ≅ associatedTriangleK S sigma' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) sorry sorry sorry

/-- Splitting independence acts by the identity on the first vertex. -/
@[simp]
theorem associatedTriangleIso_hom₁ (sigma sigma' : GradedSplitting S) :
    (associatedTriangleIso S sigma sigma').hom.hom₁ = 𝟙 _ := sorry

/-- Splitting independence acts by the identity on the second vertex. -/
@[simp]
theorem associatedTriangleIso_hom₂ (sigma sigma' : GradedSplitting S) :
    (associatedTriangleIso S sigma sigma').hom.hom₂ = 𝟙 _ := sorry

/-- Splitting independence acts by the identity on the third vertex. -/
@[simp]
theorem associatedTriangleIso_hom₃ (sigma sigma' : GradedSplitting S) :
    (associatedTriangleIso S sigma sigma').hom.hom₃ = 𝟙 _ := sorry

end DifferentialGradedModule.ShortComplex
