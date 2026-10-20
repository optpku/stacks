/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 76.9.1 (1): a thickening is a closed subspace whose associated
topological spaces agree. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsThickening :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

/- Definition 76.9.1 (2): a first-order thickening has square-zero defining
ideal sheaf. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

/- Definition 76.9.1 (3): a finite-order thickening has nilpotent defining
ideal sheaf. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

/- Definition 76.9.1 (4): an `n`th-order thickening has defining ideal sheaf
whose `(n + 1)`st power is zero. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsNthOrderThickening :
  ℕ → {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

/- Definition 76.9.1 (5): a morphism of thickenings is a commutative square of
morphisms of algebraic spaces. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.homMk :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S} →
      (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
        f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))

/- Definition 76.9.1 (6): thickenings over an algebraic space `B` and their
morphisms form the analogous arrow category in algebraic spaces over `B`. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Over :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
