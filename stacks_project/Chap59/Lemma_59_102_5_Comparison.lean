/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbelianComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.DerivedComparison

/-!
# Small-to-ph inverse-image functors

Typed compatibility entries for the abelian and bounded-below derived inverse images.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.PhComparison.aInverseImage :
    ∀ {S : Scheme.{u}} (X : Over S),
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.Scheme.PhComparison.plusAInverseImage :
    ∀ {S : Scheme.{u}} (X : Over S),
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}))
