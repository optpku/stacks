/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Computations
public import ReasLib.Algebra.Homology.HomologicalComplex.CanonicalRows
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Support

@[expose] public section

/-!
# Properties of Cartan--Eilenberg Resolutions

This module exposes the boundedness, exactness, injectivity, and support
properties of the columns of a Cartan--Eilenberg resolution.
-/

open CategoryTheory Limits HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- Every vertical column of a Cartan--Eilenberg resolution is zero in negative degrees. -/
@[stacks 015H "boundedness of Cartan-Eilenberg columns"]
instance Column.isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.column p) 0 := sorry

/-- The underlying double complex is horizontally zero below some degree. -/
@[stacks 015H "horizontal boundedness of a Cartan-Eilenberg double complex"]
theorem Bicomplex.exists_isStrictlyGE (I : CartanEilenbergResolution K) :
    ∃ p : ℤ, CochainComplex.IsStrictlyGE I.bicomplex p := sorry

/-- Every vertical column of a Cartan--Eilenberg resolution is K-injective. -/
@[stacks 015H "K-injectivity of Cartan-Eilenberg columns"]
instance Column.isKInjective (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsKInjective (I.column p) := sorry

/-- Every term of a vertical column of a Cartan--Eilenberg resolution is injective. -/
@[stacks 015H "injectivity of Cartan-Eilenberg bidegree terms"]
instance Column.injective (I : CartanEilenbergResolution K) (p q : ℤ) :
    Injective ((I.column p).X q) := sorry

/-- A vertical column of a Cartan--Eilenberg resolution vanishes in every negative degree. -/
theorem Column.isZero_of_lt_zero (I : CartanEilenbergResolution K) (p q : ℤ) (hq : q < 0) :
    IsZero ((I.column p).X q) := sorry

/-- A vertical column of a Cartan--Eilenberg resolution is exact in every positive degree. -/
theorem Column.exactAt_succ (I : CartanEilenbergResolution K) (p : ℤ) (q : ℕ) :
    (I.column p).ExactAt (Int.ofNat (q + 1)) := sorry

/-- A vertical column of a Cartan--Eilenberg resolution is exact at every positive degree. -/
theorem Column.exactAt_of_pos (I : CartanEilenbergResolution K) (p q : ℤ) (hq : 0 < q) :
    (I.column p).ExactAt q := sorry

/-- Every cycles column of a Cartan--Eilenberg resolution is K-injective. -/
instance Cycles.isKInjective (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsKInjective (I.cyclesColumn p) := sorry

/-- Every image column of a Cartan--Eilenberg resolution is K-injective. -/
instance Image.isKInjective (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsKInjective (I.imageColumn p) := sorry

/-- Every horizontal-homology column of a Cartan--Eilenberg resolution is K-injective. -/
instance Homology.isKInjective (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsKInjective (I.homologyColumn p) := sorry

/-- Every cycles column is zero in negative vertical degrees. -/
instance Cycles.isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.cyclesColumn p) 0 := sorry

/-- Every image column is zero in negative vertical degrees. -/
instance Image.isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.imageColumn p) 0 := sorry

/-- Every horizontal-homology column is zero in negative vertical degrees. -/
instance Homology.isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.homologyColumn p) 0 := sorry

/-- Every term of a cycles column is injective. -/
instance Cycles.injective (I : CartanEilenbergResolution K) (p q : ℤ) :
    Injective ((I.cyclesColumn p).X q) := sorry

/-- Every term of an image column is injective. -/
instance Image.injective (I : CartanEilenbergResolution K) (p q : ℤ) :
    Injective ((I.imageColumn p).X q) := sorry

/-- Every term of a horizontal-homology column is injective. -/
instance Homology.injective (I : CartanEilenbergResolution K) (p q : ℤ) :
    Injective ((I.homologyColumn p).X q) := sorry

/-- Horizontal cycles in every row of a Cartan--Eilenberg resolution are injective. -/
instance Row.cyclesInjective (I : CartanEilenbergResolution K) (q p : ℤ) :
    Injective (Row.cycles I q p) := sorry

/-- Horizontal differential images in every row of a Cartan--Eilenberg resolution are
injective. -/
instance Row.imageInjective (I : CartanEilenbergResolution K) (q p : ℤ) :
    Injective (Row.image I q p) := sorry

/-- Horizontal homology objects in every row of a Cartan--Eilenberg resolution are injective. -/
instance Row.homologyInjective (I : CartanEilenbergResolution K) (q p : ℤ) :
    Injective (Row.homology I q p) := sorry

/-- A cycles column vanishes in every negative degree. -/
theorem Cycles.isZero_of_lt_zero
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : q < 0) :
    IsZero ((I.cyclesColumn p).X q) := sorry

/-- An image column vanishes in every negative degree. -/
theorem Image.isZero_of_lt_zero
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : q < 0) :
    IsZero ((I.imageColumn p).X q) := sorry

/-- A horizontal-homology column vanishes in every negative degree. -/
theorem Homology.isZero_of_lt_zero
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : q < 0) :
    IsZero ((I.homologyColumn p).X q) := sorry

/-- A cycles column is exact at every positive degree. -/
theorem Cycles.exactAt_of_pos
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : 0 < q) :
    (I.cyclesColumn p).ExactAt q := sorry

/-- An image column is exact at every positive degree. -/
theorem Image.exactAt_of_pos
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : 0 < q) :
    (I.imageColumn p).ExactAt q := sorry

/-- A horizontal-homology column is exact at every positive degree. -/
theorem Homology.exactAt_of_pos
    (I : CartanEilenbergResolution K) (p q : ℤ) (hq : 0 < q) :
    (I.homologyColumn p).ExactAt q := sorry

/-- The underlying double complex has finite support on every cohomological antidiagonal. -/
@[stacks 015J "finite support of the Cartan-Eilenberg double complex"]
theorem Bicomplex.support_finite (I : CartanEilenbergResolution K) :
    HomologicalComplex₂.AntidiagonalSupport.Finite I.bicomplex := sorry

end CochainComplex.CartanEilenbergResolution
