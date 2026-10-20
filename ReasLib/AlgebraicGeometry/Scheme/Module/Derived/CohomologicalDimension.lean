/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.RightDerived.Bounds
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Limit.Truncation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import Mathlib.Order.WithBotTop

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}}

/-- Applying the total right derived functor of an additive functor to an upper-truncation
comparison induces an isomorphism on cohomology throughout the retained range, provided the
derived object has quasi-coherent cohomology. -/
theorem upperTruncation_homologyMap_isIso
    (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        ((KInjective.functor F).map ((t.truncLEι a).app E.obj))) := sorry

/-- If an additive functor preserves countable products and has bounded cohomological dimension
on quasi-coherent modules, applying its total right derived functor to the corresponding lower
truncation comparison induces an isomorphism on cohomology in the specified upper range. -/
theorem lowerTruncation_homologyMap_isIso
    (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        ((KInjective.functor F).map
          ((t.truncGEπ (b - (N : ℤ) + 1)).app E.obj))) := sorry

/-- If a derived module with quasi-coherent cohomology is supported on `[a, b]`, then applying
the total right derived functor of cohomological dimension at most `N - 1` yields cohomology
supported on `[a, b + N - 1]`. -/
theorem rightDerived_cohomology_isZero_outside
    (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (a b : EInt) (hab : a ≤ b)
    (hE : ∀ i : ℤ, (i : EInt) ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules i).obj E.obj))
    (i : ℤ) (hi : (i : EInt) ∉
      Set.Icc a (b + (((N : ℤ) - 1 : ℤ) : EInt))) :
    IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((KInjective.functor F).obj E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
