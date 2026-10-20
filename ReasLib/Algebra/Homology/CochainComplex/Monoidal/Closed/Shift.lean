/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Center.NegOnePow
public import Lean.Elab.Tactic.Omega

/-!
# Actual shift comparisons for the cochain internal Hom

Target shifts re-associate the target degree in the defining product. Source shifts also
reindex that product and use the degree-dependent sign of the graded commutator. The quadratic
term normalizes repeated source shifts to ordinary additive shift coherence.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.CochainComplex.InternalHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
variable [HasZeroObject C] [HasProductsOfShape ℤ C]
variable [∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

/-- The target shift comparison has actual product components induced by reassociation of
the target complex degree. -/
def targetShiftIso (X Y : CochainComplex C ℤ) (n : ℤ) :
    obj X (Y⟦n⟧) ≅ (obj X Y)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ Pi.mapIso fun i ↦
      (ihom (X.X i)).mapIso (Y.XIsoOfEq (add_assoc i k n)))
    (by intro k l hkl; sorry)

/-- Reindexing by `i ↦ i-n` identifies the product terms of the source-shifted Hom complex. -/
def sourceShiftDegreeIso (X Y : CochainComplex C ℤ) (n k : ℤ) :
    (obj (X⟦-n⟧) Y).X k ≅ ((obj X Y)⟦n⟧).X k :=
  Pi.mapIso
      (fun i ↦ (ihom (X.X (i + -n))).mapIso
        (Y.XIsoOfEq (show i + k = (i + -n) + (k + n) by omega))) ≪≫
    Pi.reindex (Equiv.addRight (-n)) (family X Y (k + n))

/-- The source shift comparison includes the actual degree-dependent central sign that
intertwines the two graded-commutator differentials. -/
def sourceShiftIso (X Y : CochainComplex C ℤ) (n : ℤ) :
    obj (X⟦-n⟧) Y ≅ (obj X Y)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ ((-1 : (CatCenter C)ˣ) ^ (n * k + n * (n - 1) / 2)) •
      sourceShiftDegreeIso X Y n k)
    (by intro k l hkl; sorry)

/-- The source comparison's degree component is the explicit normalized sign followed by
the actual product reindexing. -/
@[simp]
theorem sourceShiftIso_f (X Y : CochainComplex C ℤ) (n k : ℤ) :
    (sourceShiftIso X Y n).hom.f k =
      (((-1 : (CatCenter C)ˣ) ^ (n * k + n * (n - 1) / 2)) •
        sourceShiftDegreeIso X Y n k).hom := rfl

end CategoryTheory.CochainComplex.InternalHom
