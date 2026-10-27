/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

@[expose] public section

open CategoryTheory

noncomputable section

universe w wB uA uB vA vB

namespace CategoryTheory.Functor.RightDerived.KInjective

/-- An additive functor with Grothendieck-abelian source admits a total right derived functor
at its homotopy-to-derived presentation. -/
instance hasDerivedFromHomotopyPresentation
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    Functor.HasRightDerivedFunctor
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.RightDerived.KInjective.hasDerived F

end CategoryTheory.Functor.RightDerived.KInjective
