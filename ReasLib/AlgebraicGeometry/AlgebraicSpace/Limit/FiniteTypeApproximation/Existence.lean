/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Diagram

/-!
# Existence of finite-type approximation diagrams of algebraic spaces

A quasi-separated finite-type morphism to a directed inverse limit of
Noetherian algebraic spaces with affine transitions admits a good finite-type
approximation square at some stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram

/-- A quasi-separated finite-type morphism to the limit of a directed inverse
system of Noetherian algebraic spaces with affine transition morphisms admits a
finite-type approximation at some stage whose induced morphism to the
corresponding pullback is a closed immersion. -/
theorem exists_closedImmersion_of_finiteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {X : AlgebraicSpace S} (f : X ⟶ c.pt) [QuasiSeparated f] [FiniteType f] :
    ∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
      FiniteType diagram.toBi ∧
        IsClosedImmersion (pullback.lift f diagram.toW diagram.comm.w.symm) :=
  sorry

/-- Existence of a finite-type approximation diagram with closed-immersion
induced map is equivalent to existence of an intermediate algebraic space `W`
and a commuting square `X ⟶ W` over `B ⟶ B_i` with `W ⟶ B_i` of finite type
and `X ⟶ B ×_{B_i} W` a closed immersion. -/
theorem exists_closedImmersion_iff
    {I : Type u} [Preorder I]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D)
    {X : AlgebraicSpace S} (f : X ⟶ c.pt) :
    (∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
      FiniteType diagram.toBi ∧
        IsClosedImmersion (pullback.lift f diagram.toW diagram.comm.w.symm)) ↔
      ∃ (i : I) (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ D.obj i)
        (comm : CommSq toW f toBi (c.π.app i)),
        FiniteType toBi ∧
          IsClosedImmersion (pullback.lift f toW comm.w.symm) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram
