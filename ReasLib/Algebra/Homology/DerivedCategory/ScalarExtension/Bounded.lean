/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.DerivedCategory.Bounded

/-! # Preservation of upper cohomological bounds by derived scalar extension -/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

/-- Derived extension of scalars preserves cohomological boundedness above. -/
theorem derivedExtensionOfScalars_isBoundedAbove
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    ((derivedExtensionOfScalars σ).obj K).IsBoundedAbove := sorry

end CategoryTheory.ModuleCat
