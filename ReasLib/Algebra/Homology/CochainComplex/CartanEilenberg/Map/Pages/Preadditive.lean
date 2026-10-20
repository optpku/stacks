/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Preadditive

/-!
# Additive computations for Cartan--Eilenberg page maps

The page-one complexes and page-two entries are functorial images of resolution maps.  This leaf
records their additive computations so spectral-sequence and comparison code can stay at the page
API rather than unfolding homology-map implementations.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [CategoryWithHomology B]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

namespace First

/-- First page-one maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero first page-one map"]
theorem pageOne_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (Map.zero : Map I J) F q = 0 := sorry

/-- First page-one maps preserve addition. -/
@[simp, stacks 015J "additive first page-one map"]
theorem pageOne_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (f + g) F q = pageOne f F q + pageOne g F q := sorry

/-- First page-one maps preserve additive inverses. -/
@[simp]
theorem pageOne_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (-f) F q = -pageOne f F q := sorry

/-- First page-one maps preserve subtraction. -/
@[simp]
theorem pageOne_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (f - g) F q = pageOne f F q - pageOne g F q := sorry

/-- First page-one maps preserve natural-number scalar multiplication. -/
@[simp]
theorem pageOne_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (n • f) F q = n • pageOne f F q := sorry

/-- First page-one maps preserve integer scalar multiplication. -/
@[simp]
theorem pageOne_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (n • f) F q = n • pageOne f F q := sorry

/-- First page-two maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero first page-two map"]
theorem pageTwo_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (Map.zero : Map I J) F p q = 0 := sorry

/-- First page-two maps preserve addition. -/
@[simp, stacks 015J "additive first page-two map"]
theorem pageTwo_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (f + g) F p q = pageTwo f F p q + pageTwo g F p q := sorry

/-- First page-two maps preserve additive inverses. -/
@[simp]
theorem pageTwo_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (-f) F p q = -pageTwo f F p q := sorry

/-- First page-two maps preserve subtraction. -/
@[simp]
theorem pageTwo_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (f - g) F p q = pageTwo f F p q - pageTwo g F p q := sorry

/-- First page-two maps preserve natural-number scalar multiplication. -/
@[simp]
theorem pageTwo_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (n • f) F p q = n • pageTwo f F p q := sorry

/-- First page-two maps preserve integer scalar multiplication. -/
@[simp]
theorem pageTwo_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (n • f) F p q = n • pageTwo f F p q := sorry

end First

namespace Second

/-- Second page-one maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero second page-one map"]
theorem pageOne_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (Map.zero : Map I J) F q = 0 := sorry

/-- Second page-one maps preserve addition. -/
@[simp, stacks 015J "additive second page-one map"]
theorem pageOne_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (f + g) F q = pageOne f F q + pageOne g F q := sorry

/-- Second page-one maps preserve additive inverses. -/
@[simp]
theorem pageOne_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (-f) F q = -pageOne f F q := sorry

/-- Second page-one maps preserve subtraction. -/
@[simp]
theorem pageOne_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (f - g) F q = pageOne f F q - pageOne g F q := sorry

/-- Second page-one maps preserve natural-number scalar multiplication. -/
@[simp]
theorem pageOne_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (n • f) F q = n • pageOne f F q := sorry

/-- Second page-one maps preserve integer scalar multiplication. -/
@[simp]
theorem pageOne_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (n • f) F q = n • pageOne f F q := sorry

/-- Second page-two maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero second page-two map"]
theorem pageTwo_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (Map.zero : Map I J) F p q = 0 := sorry

/-- Second page-two maps preserve addition. -/
@[simp, stacks 015J "additive second page-two map"]
theorem pageTwo_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (f + g) F p q = pageTwo f F p q + pageTwo g F p q := sorry

/-- Second page-two maps preserve additive inverses. -/
@[simp]
theorem pageTwo_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (-f) F p q = -pageTwo f F p q := sorry

/-- Second page-two maps preserve subtraction. -/
@[simp]
theorem pageTwo_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (f - g) F p q = pageTwo f F p q - pageTwo g F p q := sorry

/-- Second page-two maps preserve natural-number scalar multiplication. -/
@[simp]
theorem pageTwo_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (n • f) F p q = n • pageTwo f F p q := sorry

/-- Second page-two maps preserve integer scalar multiplication. -/
@[simp]
theorem pageTwo_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (n • f) F p q = n • pageTwo f F p q := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Map
