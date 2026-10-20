/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.12.1: an algebraic stack over a scheme `S` contained in
`(Sch/S)_fppf` is a category `p : X ⟶ (Sch/S)_fppf` over `(Sch/S)_fppf` that is
a stack in groupoids, whose diagonal `Δ : X ⟶ X × X` is representable by
algebraic spaces, and that admits a scheme `U` over `S` with a surjective smooth
1-morphism `slice U ⟶ X`. -/
@[stacks 026O] #check (AlgebraicGeometry.AlgebraicStack :
  ∀ {S : Scheme.{u}}, AlgebraicGeometry.GroupoidsOver S → Prop)
