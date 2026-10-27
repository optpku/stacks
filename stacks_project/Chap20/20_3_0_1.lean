/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.EnoughInjectives
import StacksCheckRecall

@[expose] public section

/-!
# 20.3.0.1

The bounded-below derived category is the canonical `t.plus` full
subcategory, and resolution-lift calculations are owned by the generic
functorial-injective-resolution localization API.  This file deliberately
contains no chapter-local derived-category instance or resolution notation.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

section RightDerivedEquation

universe u wB vB uB

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory.{wB} B]

variable (X : AlgebraicGeometry.RingedSpace.{u})
    (F : X.Modules ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor X.Modules)
    (j' : DerivedCategory.Plus X.Modules ⥤ HomotopyCategory.Plus.Injective X.Modules)
    (h_lift : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso X.Modules) J.toFunctor j')

/- 20.3.0.1: the bounded-below right derived functor of a left exact functor
on modules over a ringed space is naturally isomorphic to its evaluation on
the lifted injective resolution `j′`. The source formula `RF = F ∘ j′` uses
termwise application of `F` followed by localization in the target. -/
@[stacks 05U3]
#check
  (CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor.isIsomorphic_rightDerived_lift
    DerivedCategory.Plus.Qh J j' h_lift
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit :
    IsIsomorphic F.rightDerivedFunctorPlus
      (j' ⋙ HomotopyCategory.Plus.Injective.ι X.Modules ⋙
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)))

end RightDerivedEquation

end
