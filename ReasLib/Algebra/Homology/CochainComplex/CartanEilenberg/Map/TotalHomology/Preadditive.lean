/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomologyFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor.Preadditive

/-!
# Additive homology maps of Cartan--Eilenberg totals

This leaf exposes zero, additive, inverse, subtraction, and scalar computation for the homology
maps induced by total and filtered-total maps.  It also registers the corresponding homology
functors as additive, so downstream spectral-sequence arguments can use typeclass inference.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- Mapped-total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on mapped-total homology"]
theorem mappedTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (zero : Map I J) F n = 0 := sorry

/-- Mapped-total homology preserves addition of resolution maps. -/
@[simp, stacks 015J "additive mapped-total homology map"]
theorem mappedTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (f + g) F n =
      mappedTotalHomology f F n + mappedTotalHomology g F n := sorry

/-- Mapped-total homology preserves additive inverses. -/
@[simp]
theorem mappedTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (-f) F n = -mappedTotalHomology f F n := sorry

/-- Mapped-total homology preserves subtraction. -/
@[simp]
theorem mappedTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (f - g) F n =
      mappedTotalHomology f F n - mappedTotalHomology g F n := sorry

/-- Mapped-total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem mappedTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q := sorry

/-- Mapped-total homology preserves integer scalar multiplication. -/
@[simp]
theorem mappedTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q := sorry

namespace First

/-- First-filtered total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on first-filtered total homology"]
theorem filteredTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (zero : Map I J) F n = 0 := sorry

/-- First-filtered total homology preserves addition. -/
@[simp, stacks 015J "additive first-filtered total homology map"]
theorem filteredTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f + g) F n =
      filteredTotalHomology f F n + filteredTotalHomology g F n := sorry

/-- First-filtered total homology preserves additive inverses. -/
@[simp]
theorem filteredTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (-f) F n = -filteredTotalHomology f F n := sorry

/-- First-filtered total homology preserves subtraction. -/
@[simp]
theorem filteredTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f - g) F n =
      filteredTotalHomology f F n - filteredTotalHomology g F n := sorry

/-- First-filtered total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := sorry

/-- First-filtered total homology preserves integer scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := sorry

end First

namespace Second

/-- Second-filtered total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on second-filtered total homology"]
theorem filteredTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (zero : Map I J) F n = 0 := sorry

/-- Second-filtered total homology preserves addition. -/
@[simp, stacks 015J "additive second-filtered total homology map"]
theorem filteredTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f + g) F n =
      filteredTotalHomology f F n + filteredTotalHomology g F n := sorry

/-- Second-filtered total homology preserves additive inverses. -/
@[simp]
theorem filteredTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (-f) F n = -filteredTotalHomology f F n := sorry

/-- Second-filtered total homology preserves subtraction. -/
@[simp]
theorem filteredTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f - g) F n =
      filteredTotalHomology f F n - filteredTotalHomology g F n := sorry

/-- Second-filtered total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := sorry

/-- Second-filtered total homology preserves integer scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Map

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Mapped-total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of mapped-total homology"]
noncomputable instance mappedTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (mappedTotalHomology F n).Additive := sorry

namespace First

/-- First-filtered total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of first-filtered total homology"]
noncomputable instance filteredTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (filteredTotalHomology F n).Additive := sorry

end First

namespace Second

/-- Second-filtered total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of second-filtered total homology"]
noncomputable instance filteredTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (filteredTotalHomology F n).Additive := sorry

end Second

#synth (mappedTotalHomology (A := A) (B := A) (𝟭 A) 0).Additive

end CochainComplex.CartanEilenbergResolution.Bundled
