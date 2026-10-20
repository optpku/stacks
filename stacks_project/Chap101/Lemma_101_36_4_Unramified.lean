/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified

/-!
# Unramified morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.isEtaleSmoothLocalAtSourceAndTarget :
  ∀ {S : Scheme.{u}},
    AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S))

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Unramified :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.unramified_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    Unramified f ↔
      DM f ∧ hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f)

#check (AlgebraicGeometry.AlgebraicStack.Unramified.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X], Unramified (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Unramified.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f],
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f)

end AlgebraicGeometry.AlgebraicStack
