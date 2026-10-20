/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.FinitelyGenerated

/-!
# Finitely generated square-zero extensions in `S`-Alg/`R`

The canonical square-zero extension functor restricts to a full subcategory
containing the extensions of all finitely generated modules.
-/

open CategoryTheory

universe u

#check (TrivSqZeroExt.fgLift :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt],
    FGModuleCat.{u} R ⥤ P.FullSubcategory)
