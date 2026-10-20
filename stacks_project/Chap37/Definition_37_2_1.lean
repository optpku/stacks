/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.2.1 (1): a thickening is a closed immersion inducing equality on the
underlying topological spaces. -/
@[stacks 04EX] #check (AlgebraicGeometry.IsThickening :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)

/- Definition 37.2.1 (2): a first-order thickening has square-zero defining ideal sheaf. -/
@[stacks 04EX] #check (AlgebraicGeometry.IsFirstOrderThickening :
  {X X' : AlgebraicGeometry.Scheme.{u}} → (X ⟶ X') → Prop)

/- Definition 37.2.1 (3): a finite-order thickening has nilpotent defining ideal sheaf. -/
@[stacks 04EX] #check (AlgebraicGeometry.IsFiniteOrderThickening :
  {X X' : AlgebraicGeometry.Scheme.{u}} → (X ⟶ X') → Prop)

/- Definition 37.2.1 (4): an `n`th-order thickening has defining ideal sheaf whose
`(n + 1)`st power is zero. -/
@[stacks 04EX] #check (AlgebraicGeometry.IsNthOrderThickening :
  ℕ → {X X' : AlgebraicGeometry.Scheme.{u}} → (X ⟶ X') → Prop)

/- Definition 37.2.1 (5): a morphism of thickenings is a commutative square of scheme
morphisms. -/
@[stacks 04EX] #check (AlgebraicGeometry.Thickening.homMk :
  {T U : AlgebraicGeometry.Thickening.{u}} →
    (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
      f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))

/- Definition 37.2.1 (6): thickenings over `S` and their morphisms form the analogous
arrow category in schemes over `S`. -/
@[stacks 04EX] #check (AlgebraicGeometry.Thickening.Over :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))
