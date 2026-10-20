/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.10.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
integral if it is representable and integral in the sense of Properties of
Stacks, Section 100.3. -/
@[stacks 0CHU] #check (AlgebraicGeometry.AlgebraicStack.IsIntegralHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

/- Definition 101.10.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
finite if it is representable and finite in the sense of Properties of
Stacks, Section 100.3. -/
@[stacks 0CHU] #check (AlgebraicGeometry.AlgebraicStack.IsFinite :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)
