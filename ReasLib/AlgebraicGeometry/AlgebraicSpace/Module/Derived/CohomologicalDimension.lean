/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.RightDerived.Bounds
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Preservation
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Grothendieck

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- For an algebraic space, the total right derived functor of a left exact additive functor
preserving countable products carries upper truncation at `a` to a cohomology isomorphism in
degrees at most `a` on derived modules with quasi-coherent cohomology. -/
theorem upperTruncation_homologyMap_isIso
    (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (quasiCoherentModuleProperty X) ((N : ℤ) - 1))
    (E : DerivedQCoh X) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        ((KInjective.functor F).map ((t.truncLEι a).app E.obj))) := sorry

/-- For an algebraic space, a left exact additive functor preserving countable products and
of cohomological dimension at most `N - 1` on quasi-coherent modules carries lower truncation
at `b - N + 1` to a derived cohomology isomorphism in degrees at least `b`. -/
theorem lowerTruncation_homologyMap_isIso
    (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (quasiCoherentModuleProperty X) ((N : ℤ) - 1))
    (E : DerivedQCoh X) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        ((KInjective.functor F).map
          ((t.truncGEπ (b - (N : ℤ) + 1)).app E.obj))) := sorry

/-- On an algebraic space, a left exact additive functor preserving countable products and
of cohomological dimension at most `N - 1` on quasi-coherent modules sends derived modules
with quasi-coherent cohomology supported on `[a, b]` to derived cohomology supported on
`[a, b + N - 1]`, allowing infinite endpoints. -/
theorem rightDerived_cohomology_isZero_outside
    (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (quasiCoherentModuleProperty X) ((N : ℤ) - 1))
    (E : DerivedQCoh X) (a b : EInt) (hab : a ≤ b)
    (hE : ∀ i : ℤ, (i : EInt) ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj))
    (i : ℤ) (hi : (i : EInt) ∉
      Set.Icc a (b + (((N : ℤ) - 1 : ℤ) : EInt))) :
    IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((KInjective.functor F).obj E.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
