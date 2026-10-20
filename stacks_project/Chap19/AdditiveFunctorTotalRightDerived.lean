/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
import StacksCheckRecall

@[expose] public section

/-!
# Chapter 19 compatibility facade

The construction-neutral and K-injective total right-derived functor APIs are owned by
`ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived`.
-/

open CategoryTheory

universe w vA uA vB uB

namespace CategoryTheory.Functor.RightDerived.KInjective

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory A] [HasDerivedCategory B]
variable (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] [HasDerived F]

@[stacks 05TH] #check
  (functor F : DerivedCategory A ⥤ DerivedCategory B)

#check @CategoryTheory.Functor.RightDerived.KInjective.unit
#check @CategoryTheory.Functor.RightDerived.KInjective.isRightDerived

end CategoryTheory.Functor.RightDerived.KInjective
