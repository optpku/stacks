/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-! # Restriction of morphisms from algebraic spaces to open subspaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The restricted morphism `W.X ⟶ X` obtained by composing the inclusion of an
open subspace of `U` with `f : U.toGroupoids ⟶ X`. -/
def openSubspaceToStack {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X)
    (W : AlgebraicSpace.OpenSubspace U) : W.X.toGroupoids ⟶ X :=
  AlgebraicSpace.toGroupoids.map W.ι ≫ f

/-- `openSubspaceToStack f W` is `toGroupoids.map W.ι ≫ f`. -/
theorem openSubspaceToStack_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X)
    (W : AlgebraicSpace.OpenSubspace U) :
    openSubspaceToStack f W = AlgebraicSpace.toGroupoids.map W.ι ≫ f :=
  rfl

end AlgebraicGeometry.AlgebraicStack
