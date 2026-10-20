/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Thin
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-source closure for two-fibre products

This leaf records the thin-fiber conclusion for a groupoid-valued two-fibre product whose two
sources are stacks in setoids. It is independent of the setoid-valued bilimit packaging.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

variable
  {S : StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J}
  {S₁ S₂ : StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J}

/-- Lemma 8.6.8 (tag 05UJ): the ambient groupoid two-fibre product of two setoid-stack
sources is a stack in setoids. This is the source-facing specialization bridge for the
generic `isStackInSetoids_of_left` closure theorem; the generic theorem owns the proof. -/
@[stacks 05UJ]
theorem isStackInSetoids_of_sources
    (F₁ : S₁.toGroupoids ⟶ S)
    (F₂ : S₂.toGroupoids ⟶ S) :
    IsStack.InSetoids J
      (StackOver.Groupoids.TwoFibreProduct.apex F₁ F₂).p := sorry

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
