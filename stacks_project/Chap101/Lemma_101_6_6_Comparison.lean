/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PullbackComparison

/-!
# Fibre-product comparison compatibility

The comparison for algebraic-space inputs is the canonical postcomposition
map, with the postcomposing morphism supplied first.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The canonical fibre-product comparison for algebraic-space inputs, with
argument order `f, x1, x2`. -/
abbrev fibreProductComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  TwoFibreProduct.mapPostcompose x1 x2 f

end AlgebraicGeometry.AlgebraicStack
