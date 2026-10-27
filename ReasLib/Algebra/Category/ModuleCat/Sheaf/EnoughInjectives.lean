/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Enough injectives for sheaves of modules on a universe-small site

Sheaves of modules have enough injectives when the site's objects and morphisms
are small in the coefficient universe and additive sheafification is available.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

/-- Sheaves of modules have enough injectives if the site's objects and morphisms
are small in the module universe and additive sheafification is available. -/
instance enoughInjectives_of_siteUnivLE {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [UnivLE.{max u v, w}]
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf J RingCat.{w}) : EnoughInjectives (SheafOfModules.{w} O) := sorry

end SheafOfModules
