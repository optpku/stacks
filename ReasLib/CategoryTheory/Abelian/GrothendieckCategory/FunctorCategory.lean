/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Enough injectives in functor categories

This leaf provides enough injectives for functor categories valued in Grothendieck abelian
categories.
-/

@[expose] public section

universe vJ uJ vA uA

namespace CategoryTheory

/-- A functor category indexed by a category small and locally small relative to the morphism
universe of its values has enough injectives when its target is Grothendieck abelian. -/
instance functorCategory_enoughInjectives
    {J : Type uJ} [Category.{vJ} J]
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [Small.{vA} J] [LocallySmall.{vA} J] [IsGrothendieckAbelian.{vA} A] :
    EnoughInjectives (J ⥤ A) :=
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives.{vA} (C := J ⥤ A)

end CategoryTheory
