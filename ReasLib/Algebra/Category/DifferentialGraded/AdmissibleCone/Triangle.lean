/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Preadditive
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangles associated to admissible cones

An admissible cone determines a triangle in the homotopy category. Both the boundary assignment
and the cone remain explicit throughout the API, since they are observable choices.
-/

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasShift (K R A) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]

namespace CompBoundaryAssignment

/-- The triangle in `K R A` associated to a graded splitting of a short complex. -/
def associatedTriangleInK (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) : Triangle (K R A) :=
  Triangle.mk S.f.inK S.g.inK
    ((B.boundary σ).inK ≫
      ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app S.X₁)

/-- The first object of the associated triangle is the first object of the short complex. -/
@[simp] theorem associatedTriangleInK_obj₁ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).obj₁ = S.X₁.inK := sorry

/-- The second object of the associated triangle is the middle object of the short complex. -/
@[simp] theorem associatedTriangleInK_obj₂ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).obj₂ = S.X₂.inK := sorry

/-- The third object of the associated triangle is the last object of the short complex. -/
@[simp] theorem associatedTriangleInK_obj₃ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).obj₃ = S.X₃.inK := sorry

/-- The first morphism of the associated triangle is the first short-complex map. -/
@[simp] theorem associatedTriangleInK_mor₁ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).mor₁ = S.f.inK := sorry

/-- The second morphism of the associated triangle is the second short-complex map. -/
@[simp] theorem associatedTriangleInK_mor₂ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).mor₂ = S.g.inK := sorry

/-- The final morphism of the associated triangle is the boundary of the graded splitting. -/
@[simp] theorem associatedTriangleInK_mor₃ (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (B.associatedTriangleInK σ).mor₃ =
      (B.boundary σ).inK ≫
        ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app S.X₁ := sorry

/-- Lemma 22.27.9 (09QQ): the associated triangle is canonically independent of the chosen
graded splitting, through the identity on all three vertices. -/
@[stacks 09QQ]
def associatedTriangleIso (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ τ : S.GradedSplitting) :
    B.associatedTriangleInK σ ≅ B.associatedTriangleInK τ :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) sorry sorry sorry

/-- Boundary morphisms from two graded splittings have the same class in `K R A`. -/
theorem boundary_inK_eq (B : CompBoundaryAssignment R A)
    {S : ShortComplex (Comp R A)} (σ τ : S.GradedSplitting) :
    (B.boundary σ).inK = (B.boundary τ).inK := sorry

end CompBoundaryAssignment

namespace AdmissibleBoundary

variable [ShiftCompatibility R A]

/-- Lemma 22.27.1 (09P6): the triangle in `K R A` canonically associated to a graded-split
short complex. -/
@[stacks 09P6 "triangle of a graded-split sequence in the DG homotopy category"]
def triangleInK {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    Triangle (K R A) :=
  (assignment (R := R) (A := A)).associatedTriangleInK σ

/-- The first two maps of the canonical graded-split triangle compose to zero. -/
theorem triangleInK_comp_zero₁₂ {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (triangleInK σ).mor₁ ≫ (triangleInK σ).mor₂ = 0 := sorry

/-- The second and third maps of the canonical graded-split triangle compose to zero. -/
theorem triangleInK_comp_zero₂₃ {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (triangleInK σ).mor₂ ≫ (triangleInK σ).mor₃ = 0 := sorry

/-- The third map followed by the shift of the first map composes to zero. -/
theorem triangleInK_comp_zero₃₁ {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (triangleInK σ).mor₃ ≫ (triangleInK σ).mor₁⟦(1 : ℤ)⟧' = 0 := sorry

end AdmissibleBoundary

namespace CompBoundaryAssignment.AdmissibleCone

/-- The triangle in `K R A` determined by the explicit admissible cone `C`. -/
def triangleInK {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    Triangle (K R A) :=
  Triangle.mk f.inK C.toCone.inK
    (-C.toShift.inK ≫
      ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app x)

/-- The first object of the triangle associated to `C` is the source of its defining map. -/
@[simp] theorem triangleInK_obj₁ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.obj₁ = x.inK := sorry

/-- The second object of the triangle associated to `C` is the target of its defining map. -/
@[simp] theorem triangleInK_obj₂ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.obj₂ = y.inK := sorry

/-- The third object of the triangle associated to `C` is its cone object in `K R A`. -/
@[simp] theorem triangleInK_obj₃ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.obj₃ = C.obj.inK := sorry

/-- The first map of the triangle associated to `C` is the image of its defining map. -/
@[simp] theorem triangleInK_mor₁ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.mor₁ = f.inK := sorry

/-- The second map of the triangle associated to `C` is the image of its cone inclusion. -/
@[simp] theorem triangleInK_mor₂ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.mor₂ = C.toCone.inK := sorry

/-- The third map of the cone triangle is the negative shifted cone projection in `K R A`. -/
@[simp] theorem triangleInK_mor₃ {x y : Comp R A} {f : x ⟶ y} (C : B.AdmissibleCone f) :
    C.triangleInK.mor₃ =
      -C.toShift.inK ≫
        ((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app x := sorry

/-- Assemble a morphism of admissible-cone triangles from its three maps and commutative
squares. The square proofs are explicit law inputs; the three morphisms are the data. -/
def homInK {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    C₁.triangleInK ⟶ C₂.triangleInK :=
  Triangle.homMk _ _ a.inK b.inK c.inK sq₁.w sq₂.w sq₃.w

/-- The first component of `homInK` is the image of `a`. -/
@[simp] theorem homInK_hom₁ {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₁ = a.inK := sorry

/-- The second component of `homInK` is the image of `b`. -/
@[simp] theorem homInK_hom₂ {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₂ = b.inK := sorry

/-- The third component of `homInK` is the image of the cone map `c`. -/
@[simp] theorem homInK_hom₃ {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₃ = c.inK := sorry

section Pretriangulated

variable [Limits.HasZeroObject (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]
variable [Pretriangulated (K R A)]

/-- The specialized two-out-of-three principle for a morphism of admissible-cone triangles.
The two membership hypotheses explicitly connect the cones to the chosen pretriangulation. -/
theorem isIso_coneMap {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃)
    (hC₁ : C₁.triangleInK ∈ distTriang (K R A))
    (hC₂ : C₂.triangleInK ∈ distTriang (K R A))
    (ha : IsIso a.inK) (hb : IsIso b.inK) : IsIso c.inK := sorry

end Pretriangulated

/-- Lemma 22.27.12 (09QT): a map between explicit admissible cones whose first two maps are
homotopy equivalences is itself a homotopy equivalence when the three maps form a morphism of the
associated triangles in `K R A`. -/
@[stacks 09QT]
theorem homotopyEquivalences_coneMap
    {x₁ y₁ x₂ y₂ : Comp R A} {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂}
    (C₁ : B.AdmissibleCone f₁) (C₂ : B.AdmissibleCone f₂)
    {a : x₁ ⟶ x₂} {b : y₁ ⟶ y₂} {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃)
    (ha : Comp.homotopyEquivalences a) (hb : Comp.homotopyEquivalences b) :
    Comp.homotopyEquivalences c := sorry

end CompBoundaryAssignment.AdmissibleCone

end DifferentialGradedCategory
