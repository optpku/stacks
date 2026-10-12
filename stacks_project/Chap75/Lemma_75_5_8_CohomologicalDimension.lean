/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.WithBotTop
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsGrothendieckAbelian.{u} (Modules X)]

/-- Applying the total right derived functor of a left exact additive functor that preserves
countable products to an upper-truncation comparison induces an isomorphism on cohomology
throughout the retained range, provided the derived object has quasi-coherent cohomology. -/
theorem upperTruncation_homologyMap_isIso
    (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
      (quasiCoherentModuleProperty X) ((N : ℤ) - 1))
    (E : DerivedQCoh X) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        ((KInjective.functor F).map ((t.truncLEι a).app E.obj))) := sorry

/-- If a left exact additive functor preserves countable products and has bounded cohomological
dimension on quasi-coherent modules, applying its total right derived functor to the
corresponding lower truncation comparison induces an isomorphism on cohomology in the
specified upper range. -/
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

/-- If a derived module with quasi-coherent cohomology is supported on `[a, b]`, then applying
the total right derived functor of a left exact countable-product-preserving functor of
cohomological dimension at most `N - 1` yields cohomology supported on `[a, b + N - 1]`. -/
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
