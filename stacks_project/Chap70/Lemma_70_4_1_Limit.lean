/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit

/-!
# Directed affine inverse limits of algebraic spaces

The directed affine limit and its affine projections are supplied by the
shared algebraic-space limit construction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (IsLimit)

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit_functorOfPoints :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit D).functorOfPoints =
        Limits.limit (D ⋙ AlgebraicGeometry.AlgebraicSpace.forgetToPresheaf))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.affine_π :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      ∀ (i : OrderDual I), Affine (Limits.limit.π D i))
