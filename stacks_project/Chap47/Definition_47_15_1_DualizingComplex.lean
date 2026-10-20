/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing

universe u

/- Compatibility check for the ring-level dualizing-complex predicate. -/
#check (@CategoryTheory.DerivedCategory.IsDualizingComplex :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    [CategoryTheory.MonoidalCategory
      (_root_.DerivedCategory (ModuleCat.{u} A))] →
    _root_.DerivedCategory (ModuleCat.{u} A) →
    CategoryTheory.MonoidalClosed
      (_root_.DerivedCategory (ModuleCat.{u} A)) → Prop)
