/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare.ClosedPoint

/-!
# Closed points of valuative squares of algebraic stacks

The closed point of `Spec(R)` in a valuative square of algebraic stacks is
compared with `|Y|` along the bottom map of the square.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.closedPoint :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (sq : ValuativeCommSq f), sq.specR.left)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.closedPointImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    ValuativeCommSq f → Points Y)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.closedPointImage_spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (sq : ValuativeCommSq f),
    sq.closedPointImage = Points.mapOfSlice sq.i₂ sq.closedPoint)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.closedPoint_eq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (sq : ValuativeCommSq f), sq.closedPoint = IsLocalRing.closedPoint sq.R)

end AlgebraicGeometry.AlgebraicStack
