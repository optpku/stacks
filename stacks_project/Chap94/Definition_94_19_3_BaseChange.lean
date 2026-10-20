/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

#check (AlgebraicGeometry.AlgebraicStack.baseChange :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicStack.baseChange_eq :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    AlgebraicStack.baseChange g X' =
      FiberedCategoryOver.Groupoids.pullback.{u + 1, u + 1, u + 1, u, u, u}
        (Over.map g) X')

#check (AlgebraicGeometry.AlgebraicStack.baseChange_total :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    (AlgebraicStack.baseChange g X').total = CategoricalPullback (Over.map g) X'.p)

#check (AlgebraicGeometry.AlgebraicStack.baseChange_p :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    (AlgebraicStack.baseChange g X').p = CategoricalPullback.π₁ (Over.map g) X'.p)

#check (AlgebraicGeometry.AlgebraicStack.instBaseChange :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    AlgebraicStack (AlgebraicStack.baseChange g X'))

#check (AlgebraicGeometry.AlgebraicStack.baseChange_spec :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    (AlgebraicStack.baseChange g X').total = CategoricalPullback (Over.map g) X'.p ∧
      (AlgebraicStack.baseChange g X').p = CategoricalPullback.π₁ (Over.map g) X'.p)

#check (AlgebraicGeometry.AlgebraicStacks.baseChange :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : AlgebraicStacks S'), AlgebraicStacks S)

#check (AlgebraicGeometry.AlgebraicStacks.baseChange_toGroupoids :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : AlgebraicStacks S'),
    AlgebraicStacks.toGroupoids (AlgebraicStacks.baseChange g X') =
      AlgebraicStack.baseChange g (AlgebraicStacks.toGroupoids X'))
