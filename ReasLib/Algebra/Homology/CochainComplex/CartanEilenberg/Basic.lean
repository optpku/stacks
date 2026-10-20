/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Row
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cartan--Eilenberg Resolutions

This module owns the data of a Cartan--Eilenberg resolution of a bounded-below
cochain complex.  It is independent of a particular derived-functor or
spectral-sequence construction: those applications can consume the row,
column, and resolution views exposed here.
-/

open CategoryTheory Limits HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A Cartan--Eilenberg resolution of a bounded-below cochain complex `K`.

It consists of a horizontally bounded-below double complex with an augmentation from `K`,
together with compatible injective resolutions of its columns, cycle columns, image columns,
and horizontal-homology columns. -/
@[stacks 015H]
structure CartanEilenbergResolution (K : CochainComplex.Plus A) where
  /-- The horizontally bounded-below double complex underlying the resolution. -/
  doubleComplex : CochainComplex.Plus (CochainComplex A ℤ)
  /-- The augmentation from `K` to the bottom row. -/
  ε : K.obj ⟶ (flip doubleComplex.obj).X 0
  /-- A chosen injective resolution of the `p`-th term of `K`. -/
  columnResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.X p)
  /-- The chosen column resolution identifies with the actual `p`-th column. -/
  columnIso (p : ℤ) : (columnResolution p).cochainComplex ≅ doubleComplex.obj.X p
  /-- The degree-zero column augmentation agrees with the bottom-row augmentation. -/
  columnAugmentation_f_zero (p : ℤ) :
    ((columnResolution p).ι' ≫ (columnIso p).hom).f 0 = ε.f p
  /-- A chosen injective resolution of the `p`-th cycles object of `K`. -/
  cyclesResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.cycles p)
  /-- The cycles resolution identifies with the cycles complex of the `p`-th horizontal map. -/
  cyclesIso (p : ℤ) :
    (cyclesResolution p).cochainComplex ≅ doubleComplex.obj.cycles p
  /-- The degree-zero cycles augmentation is induced by the global augmentation. -/
  cyclesAugmentation_f_zero (p : ℤ) :
    ((cyclesResolution p).ι' ≫ (cyclesIso p).hom).f 0 =
      doubleComplex.obj.rowCyclesMap ε p
  /-- A chosen injective resolution of the image of the `p`-th horizontal map of `K`. -/
  imageResolution (p : ℤ) :
    CategoryTheory.InjectiveResolution (image (K.obj.d p (p + 1)))
  /-- The image resolution identifies with the image complex of the `p`-th horizontal map. -/
  imageIso (p : ℤ) :
    (imageResolution p).cochainComplex ≅ image (doubleComplex.obj.d p (p + 1))
  /-- The degree-zero image augmentation is induced by the global augmentation. -/
  imageAugmentation_f_zero (p : ℤ) :
    ((imageResolution p).ι' ≫ (imageIso p).hom).f 0 =
      doubleComplex.obj.rowImageMap ε p (p + 1)
  /-- A chosen injective resolution of the `p`-th cohomology object of `K`. -/
  homologyResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.homology p)
  /-- The homology resolution identifies with the horizontal-homology complex in degree `p`. -/
  homologyIso (p : ℤ) :
    (homologyResolution p).cochainComplex ≅ doubleComplex.obj.homology p
  /-- The degree-zero homology augmentation is induced by the global augmentation. -/
  homologyAugmentation_f_zero (p : ℤ) :
    ((homologyResolution p).ι' ≫ (homologyIso p).hom).f 0 =
      doubleComplex.obj.rowHomologyMap ε p

namespace CartanEilenbergResolution

variable {K : CochainComplex.Plus A}

/-- The cohomological double complex underlying a Cartan--Eilenberg resolution.

This view forgets only the bounded-below packaging on the horizontal complex, so clients can
apply the ordinary double-complex API without repeatedly projecting through `doubleComplex.obj`.
-/
@[stacks 015H "the underlying Cartan-Eilenberg double complex"]
abbrev bicomplex (I : CartanEilenbergResolution K) :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  I.doubleComplex.obj

/-- The horizontally bounded-below packaging of the underlying double complex. -/
@[stacks 015H "the bounded-below horizontal Cartan-Eilenberg complex"]
abbrev horizontalPlus (I : CartanEilenbergResolution K) :
    CochainComplex.plus (CochainComplex A ℤ) I.bicomplex :=
  I.doubleComplex.property

/-- The bottom row of a Cartan--Eilenberg double complex. -/
@[stacks 015H "the bottom row of a Cartan-Eilenberg resolution"]
abbrev bottomRow (I : CartanEilenbergResolution K) : CochainComplex A ℤ :=
  (flip I.bicomplex).X 0

/-- The augmentation of a Cartan--Eilenberg resolution as a morphism to its bottom row. -/
@[stacks 015H "the Cartan-Eilenberg augmentation"]
abbrev augmentation (I : CartanEilenbergResolution K) : K.obj ⟶ I.bottomRow :=
  I.ε

/-- The vertical cochain complex in horizontal degree `p`. -/
@[stacks 015H "a Cartan-Eilenberg column"]
abbrev column (I : CartanEilenbergResolution K) (p : ℤ) : CochainComplex A ℤ :=
  I.bicomplex.X p

/-- The horizontal cochain complex in vertical degree `q`. -/
@[stacks 015H "a Cartan-Eilenberg row"]
abbrev row (I : CartanEilenbergResolution K) (q : ℤ) : CochainComplex A ℤ :=
  I.bicomplex.flip.X q

/-- The object of the underlying double complex in bidegree `(p, q)`. -/
@[stacks 015H "a Cartan-Eilenberg bidegree term"]
abbrev term (I : CartanEilenbergResolution K) (p q : ℤ) : A :=
  (I.column p).X q

/-- The cycles cochain complex in horizontal degree `p`. -/
@[stacks 015H "a Cartan-Eilenberg cycles column"]
abbrev cyclesColumn (I : CartanEilenbergResolution K) (p : ℤ) : CochainComplex A ℤ :=
  I.bicomplex.cycles p

/-- The image cochain complex of the horizontal differential in degree `p`. -/
@[stacks 015H "a Cartan-Eilenberg image column"]
abbrev imageColumn (I : CartanEilenbergResolution K) (p : ℤ) : CochainComplex A ℤ :=
  image (I.bicomplex.d p (p + 1))

/-- The horizontal-homology cochain complex in degree `p`. -/
@[stacks 015H "a Cartan-Eilenberg homology column"]
abbrev homologyColumn (I : CartanEilenbergResolution K) (p : ℤ) : CochainComplex A ℤ :=
  I.bicomplex.homology p

/-- The chosen column resolution, identified with the actual vertical column. -/
abbrev Column.resolutionIso (I : CartanEilenbergResolution K) (p : ℤ) :
    (I.columnResolution p).cochainComplex ≅ I.column p :=
  I.columnIso p

/-- The chosen cycles resolution, identified with the cycles complex of the corresponding
horizontal differential. -/
abbrev Cycles.resolutionIso (I : CartanEilenbergResolution K) (p : ℤ) :
    (I.cyclesResolution p).cochainComplex ≅ I.cyclesColumn p :=
  I.cyclesIso p

/-- The chosen image resolution, identified with the image complex of the corresponding
horizontal differential. -/
abbrev Image.resolutionIso (I : CartanEilenbergResolution K) (p : ℤ) :
    (I.imageResolution p).cochainComplex ≅ I.imageColumn p :=
  I.imageIso p

/-- The chosen cohomology resolution, identified with the horizontal-homology complex in the
same degree. -/
abbrev Homology.resolutionIso (I : CartanEilenbergResolution K) (p : ℤ) :
    (I.homologyResolution p).cochainComplex ≅ I.homologyColumn p :=
  I.homologyIso p

end CartanEilenbergResolution

end CochainComplex
