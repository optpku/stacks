/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase.OverSlice
import StacksCheckRecall

/-!
# Algebraic stacks over a slice algebraic stack

This source-facing module exposes the canonical algebraic-stack strict-slice carrier.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStacks

#check (overSlice : ∀ {S S' : Scheme.{u}}, (S ⟶ S') → AlgebraicStacks S')
#check (OverSlice : ∀ {S S' : Scheme.{u}}, (S ⟶ S') → Type (u + 2))
#check (OverSlice.mk : ∀ {S S' : Scheme.{u}} {g : S ⟶ S'}, ∀ (X' : AlgebraicStacks S'), (X' ⟶ overSlice g) → OverSlice g)

end AlgebraicGeometry.AlgebraicStacks
