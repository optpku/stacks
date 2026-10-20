module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Rows
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Augmentations of Cartan--Eilenberg resolution columns

This file provides parallel augmentations for the term, cycles, differential-image, and homology
columns, together with their degree-zero computations.
-/

open CategoryTheory Limits

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- The augmentation of the chosen injective resolution into the actual `p`-th column. -/
@[stacks 015H "column-resolution augmentation"]
abbrev Column.Augmentation.map (I : CartanEilenbergResolution K) (p : ℤ) :
    (CochainComplex.singleFunctor A 0).obj (K.obj.X p) ⟶ I.column p :=
  (I.columnResolution p).ι' ≫ (Column.resolutionIso I p).hom

/-- The augmentation of the chosen cycles resolution into the horizontal cycles column. -/
@[stacks 015H "cycles-resolution augmentation"]
abbrev Cycles.Augmentation.map (I : CartanEilenbergResolution K) (p : ℤ) :
    (CochainComplex.singleFunctor A 0).obj (K.obj.cycles p) ⟶ I.cyclesColumn p :=
  (I.cyclesResolution p).ι' ≫ (Cycles.resolutionIso I p).hom

/-- The augmentation of the chosen image resolution into the horizontal differential-image
column. -/
@[stacks 015H "image-resolution augmentation"]
abbrev Image.Augmentation.map (I : CartanEilenbergResolution K) (p : ℤ) :
    (CochainComplex.singleFunctor A 0).obj (image (K.obj.d p (p + 1))) ⟶
      I.imageColumn p :=
  (I.imageResolution p).ι' ≫ (Image.resolutionIso I p).hom

/-- The augmentation of the chosen homology resolution into the horizontal-homology column. -/
@[stacks 015H "homology-resolution augmentation"]
abbrev Homology.Augmentation.map (I : CartanEilenbergResolution K) (p : ℤ) :
    (CochainComplex.singleFunctor A 0).obj (K.obj.homology p) ⟶ I.homologyColumn p :=
  (I.homologyResolution p).ι' ≫ (Homology.resolutionIso I p).hom

/-- The component in bidegree `(p, 0)` of the Cartan--Eilenberg augmentation. -/
@[stacks 015H "Cartan-Eilenberg augmentation component"]
abbrev Augmentation.component (I : CartanEilenbergResolution K) (p : ℤ) :
    K.obj.X p ⟶ I.term p 0 :=
  I.augmentation.f p

/-- The degree-zero component of the chosen column augmentation. -/
abbrev Column.Augmentation.zero (I : CartanEilenbergResolution K) (p : ℤ) :
    K.obj.X p ⟶ I.term p 0 :=
  (Column.Augmentation.map I p).f 0

/-- The degree-zero component of the chosen cycles augmentation. -/
abbrev Cycles.Augmentation.zero (I : CartanEilenbergResolution K) (p : ℤ) :
    K.obj.cycles p ⟶ (I.cyclesColumn p).X 0 :=
  (Cycles.Augmentation.map I p).f 0

/-- The degree-zero component of the chosen image augmentation. -/
abbrev Image.Augmentation.zero (I : CartanEilenbergResolution K) (p : ℤ) :
    image (K.obj.d p (p + 1)) ⟶ (I.imageColumn p).X 0 :=
  (Image.Augmentation.map I p).f 0

/-- The degree-zero component of the chosen homology augmentation. -/
abbrev Homology.Augmentation.zero (I : CartanEilenbergResolution K) (p : ℤ) :
    K.obj.homology p ⟶ (I.homologyColumn p).X 0 :=
  (Homology.Augmentation.map I p).f 0

/-- The zero-degree column augmentation is the corresponding component of the global
Cartan--Eilenberg augmentation. -/
@[simp]
theorem Column.Augmentation.zero_eq_component
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Column.Augmentation.zero I p = Augmentation.component I p := sorry

/-- The zero-degree cycles augmentation is the map on cycles induced by the global
Cartan--Eilenberg augmentation. -/
@[simp]
theorem Cycles.Augmentation.zero_eq_rowMap
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Cycles.Augmentation.zero I p = I.bicomplex.rowCyclesMap I.augmentation p := sorry

/-- The zero-degree image augmentation is the map on differential images induced by the global
Cartan--Eilenberg augmentation. -/
@[simp]
theorem Image.Augmentation.zero_eq_rowMap
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Image.Augmentation.zero I p = I.bicomplex.rowImageMap I.augmentation p (p + 1) := sorry

/-- The zero-degree homology augmentation is the map on homology induced by the global
Cartan--Eilenberg augmentation. -/
@[simp]
theorem Homology.Augmentation.zero_eq_rowMap
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Homology.Augmentation.zero I p = I.bicomplex.rowHomologyMap I.augmentation p := sorry

/-- Every zero-degree column augmentation lands in cycles of its vertical column. -/
@[reassoc (attr := simp)]
theorem Column.Augmentation.zero_comp_d
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Column.Augmentation.zero I p ≫ (I.column p).d 0 1 = 0 := sorry

/-- The global Cartan--Eilenberg augmentation lands in vertical cycles in bidegree `(p, 0)`. -/
@[reassoc (attr := simp)]
theorem Augmentation.component_comp_d
    (I : CartanEilenbergResolution K) (p : ℤ) :
    Augmentation.component I p ≫ (I.column p).d 0 1 = 0 := sorry

end CochainComplex.CartanEilenbergResolution
