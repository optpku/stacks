/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.Over.Square
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Squares of unbounded derived pullback functors on slice sites

The square of continuous pullback functors attached to a commutative square acts canonically on
unbounded derived categories because every pullback functor is exact on abelian sheaves.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Over.Pullback

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {X' X Y' Y : C}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [HasSheafify (J.over X') AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y') AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y) AddCommGrpCat.{max u v}]

/-- The derived inverse-image square associated to a commutative square in the base category. -/
@[stacks 015F "derived inverse-image square on slice sites"]
noncomputable def squareIso (hcomm : i ≫ f = p ≫ g) :
    Over.pullback J g ⋙ Over.pullback J p ≅
      Over.pullback J f ⋙ Over.pullback J i :=
  ExactFunctor.MapDerivedCategory.squareIso
    (Over.pullbackExact J g) (Over.pullbackExact J p)
    (Over.pullbackExact J f) (Over.pullbackExact J i)
    ((exactFunctor _ _).isoMk
      (J.overMapPullbackSquare AddCommGrpCat.{max u v} i p f g hcomm).symm)

end CategoryTheory.GrothendieckTopology.Derived.Over.Pullback

end
