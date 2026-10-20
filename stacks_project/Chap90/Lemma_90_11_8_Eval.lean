/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.Evaluation

/-!
# Evaluation of a functor on finitely generated square-zero extensions

Evaluation along the restricted square-zero extension functor sends a module
`M` to the value `F(R[M])`.
-/

open CategoryTheory

universe u

#check (CategoryTheory.Functor.fgEval :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u), FGModuleCat.{u} R ⥤ Type u)
