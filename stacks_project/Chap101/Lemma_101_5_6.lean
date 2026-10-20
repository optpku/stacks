/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Monomorphism
import StacksCheckRecall

/-!
# Monomorphisms of algebraic stacks and inertia squares

If `f : X ⟶ Y` is a monomorphism of algebraic stacks, the square with vertices
`I_X`, `X`, `I_Y`, and `Y` is a 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.5.6: Let `f : X ⟶ Y` be a monomorphism of algebraic stacks.
Then the diagram with vertices `I_X`, `X`, `I_Y`, and `Y`, horizontal legs
`Inertia.forget X` and `Inertia.forget Y`, and vertical legs `Inertia.map f`
and `f`, is a fibre product square. -/
@[stacks 06R5] #check
  (AlgebraicGeometry.AlgebraicStack.Inertia.mapForgetCone.isBilimit :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f],
      (AlgebraicGeometry.AlgebraicStack.Inertia.mapForgetCone f).IsBilimit)
