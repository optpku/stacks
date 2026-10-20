/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Interval
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Stage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A proper smooth scheme over a field has a finite locally free module whose bounded shifts
generate every coherent module in a uniformly bounded positive additive extension stage. -/
theorem exists_finiteLocallyFree_additiveExtensionStage
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [Smooth f] :
    ∃ (m n : ℕ+) (G : X.Modules), SheafOfModules.IsFiniteLocallyFree G ∧
      ∀ (F : X.Modules), SheafOfModules.IsCoherent (R := X.ringCatSheaf) F →
        additiveExtensionStage
          (objectShiftInterval
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj G)
            (-(m : ℤ)) (m : ℤ))
          n
          ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
