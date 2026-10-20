/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total

/-!
# Additive total maps of Cartan--Eilenberg resolutions

The total, mapped-total, and filtered-total views of a fixed Cartan--Eilenberg resolution map
inherit its additive operations.  This leaf keeps those computation lemmas close to the total-map
owner so downstream arguments need not unfold totalization.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- Totalization sends the zero Cartan--Eilenberg resolution map to the zero cochain map. -/
@[simp, stacks 015J "zero total map of Cartan-Eilenberg resolutions"]
theorem total_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) :
    total (zero : Map I J) = 0 := sorry

/-- Totalization preserves addition of fixed Cartan--Eilenberg resolution maps. -/
@[simp, stacks 015J "additive total map of Cartan-Eilenberg resolutions"]
theorem total_add (f g : Map I J) :
    total (f + g) = total f + total g := sorry

/-- Totalization preserves additive inverses of fixed Cartan--Eilenberg resolution maps. -/
@[simp]
theorem total_neg (f : Map I J) :
    total (-f) = -total f := sorry

/-- Totalization preserves subtraction of fixed Cartan--Eilenberg resolution maps. -/
@[simp]
theorem total_sub (f g : Map I J) :
    total (f - g) = total f - total g := sorry

/-- Totalization preserves natural-number scalar multiplication. -/
@[simp]
theorem total_nsmul (n : ℕ) (f : Map I J) :
    total (n • f) = n • total f := sorry

/-- Totalization preserves integer scalar multiplication. -/
@[simp]
theorem total_zsmul (n : ℤ) (f : Map I J) :
    total (n • f) = n • total f := sorry

/-- The bounded-below total map of the zero resolution map is zero. -/
@[simp]
theorem totalPlus_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) :
    totalPlus (zero : Map I J) = 0 := sorry

/-- The bounded-below total construction preserves addition. -/
@[simp]
theorem totalPlus_add (f g : Map I J) :
    totalPlus (f + g) = totalPlus f + totalPlus g := sorry

/-- The bounded-below total construction preserves additive inverses. -/
@[simp]
theorem totalPlus_neg (f : Map I J) :
    totalPlus (-f) = -totalPlus f := sorry

/-- The bounded-below total construction preserves subtraction. -/
@[simp]
theorem totalPlus_sub (f g : Map I J) :
    totalPlus (f - g) = totalPlus f - totalPlus g := sorry

/-- The bounded-below total construction preserves natural-number scalar multiplication. -/
@[simp]
theorem totalPlus_nsmul (n : ℕ) (f : Map I J) :
    totalPlus (n • f) = n • totalPlus f := sorry

/-- The bounded-below total construction preserves integer scalar multiplication. -/
@[simp]
theorem totalPlus_zsmul (n : ℤ) (f : Map I J) :
    totalPlus (n • f) = n • totalPlus f := sorry

section Mapped

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Additive functors send a zero Cartan--Eilenberg map to a zero mapped-total map. -/
@[simp, stacks 015J "zero mapped-total map of Cartan-Eilenberg resolutions"]
theorem mappedTotal_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] :
    mappedTotal (zero : Map I J) F = 0 := sorry

/-- Additive functors preserve addition of mapped Cartan--Eilenberg total maps. -/
@[simp]
theorem mappedTotal_add (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    mappedTotal (f + g) F = mappedTotal f F + mappedTotal g F := sorry

/-- Additive functors preserve additive inverses of mapped Cartan--Eilenberg total maps. -/
@[simp]
theorem mappedTotal_neg (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mappedTotal (-f) F = -mappedTotal f F := sorry

/-- Additive functors preserve subtraction of mapped Cartan--Eilenberg total maps. -/
@[simp]
theorem mappedTotal_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    mappedTotal (f - g) F = mappedTotal f F - mappedTotal g F := sorry

/-- Additive functors preserve natural-number multiples of mapped-total maps. -/
@[simp]
theorem mappedTotal_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mappedTotal (n • f) F = n • mappedTotal f F := sorry

/-- Additive functors preserve integer multiples of mapped-total maps. -/
@[simp]
theorem mappedTotal_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mappedTotal (n • f) F = n • mappedTotal f F := sorry

namespace First

/-- The first-filtered total map of the zero resolution map is zero. -/
@[simp]
theorem filteredTotal_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] :
    filteredTotal (zero : Map I J) F = 0 := sorry

/-- The first-filtered total construction preserves addition. -/
@[simp]
theorem filteredTotal_add (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (f + g) F = filteredTotal f F + filteredTotal g F := sorry

/-- The first-filtered total construction preserves additive inverses. -/
@[simp]
theorem filteredTotal_neg (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (-f) F = -filteredTotal f F := sorry

/-- The first-filtered total construction preserves subtraction. -/
@[simp]
theorem filteredTotal_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (f - g) F = filteredTotal f F - filteredTotal g F := sorry

/-- The first-filtered total construction preserves natural-number multiples. -/
@[simp]
theorem filteredTotal_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (n • f) F = n • filteredTotal f F := sorry

/-- The first-filtered total construction preserves integer multiples. -/
@[simp]
theorem filteredTotal_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (n • f) F = n • filteredTotal f F := sorry

end First

namespace Second

/-- The second-filtered total map of the zero resolution map is zero. -/
@[simp]
theorem filteredTotal_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] :
    filteredTotal (zero : Map I J) F = 0 := sorry

/-- The second-filtered total construction preserves addition. -/
@[simp]
theorem filteredTotal_add (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (f + g) F = filteredTotal f F + filteredTotal g F := sorry

/-- The second-filtered total construction preserves additive inverses. -/
@[simp]
theorem filteredTotal_neg (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (-f) F = -filteredTotal f F := sorry

/-- The second-filtered total construction preserves subtraction. -/
@[simp]
theorem filteredTotal_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (f - g) F = filteredTotal f F - filteredTotal g F := sorry

/-- The second-filtered total construction preserves natural-number multiples. -/
@[simp]
theorem filteredTotal_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (n • f) F = n • filteredTotal f F := sorry

/-- The second-filtered total construction preserves integer multiples. -/
@[simp]
theorem filteredTotal_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    filteredTotal (n • f) F = n • filteredTotal f F := sorry

end Second

end Mapped

end CochainComplex.CartanEilenbergResolution.Map
