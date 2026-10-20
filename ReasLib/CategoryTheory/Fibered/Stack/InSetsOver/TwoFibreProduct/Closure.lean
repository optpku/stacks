/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Discrete
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-source specialization of two-fibre-product closure

This leaf specializes the neutral groupoid-stack closure theorem to a setoid-stack cospan whose
two sources are bundled stacks in sets.  The reusable proof owner remains in
`StackOver.Groupoids.TwoFibreProduct`.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.TwoFibreProduct

variable
  {S : StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J}
  {S₁ S₂ : StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The explicit setoid-stack two-fibre product of two set-stack sources is a stack in sets.
This is the bundled-source specialization of the neutral
`StackOver.Groupoids.TwoFibreProduct.isStackInSets` closure theorem. -/
@[stacks 0047 "set-stack-source stack closure"]
theorem isStackInSets_of_sources
    (F₁ : S₁.toSetoids ⟶ S) (F₂ : S₂.toSetoids ⟶ S) :
    IsStack.InSets J
      (StackOver.Setoids.TwoFibreProduct.apex F₁ F₂).p := sorry

/-- The original source-facing closure owner: the explicit setoid-stack two-fibre product of two
set-stack sources has a discrete projection. The stronger stack-in-sets companion above is
separate, so consumers that only need discreteness do not acquire a stronger proposition. -/
@[stacks 0047 "set-stack-source discrete-fibration closure"]
theorem isDiscreteFibration_of_sources
    (F₁ : S₁.toSetoids ⟶ S) (F₂ : S₂.toSetoids ⟶ S) :
    Functor.IsDiscreteFibration
      (StackOver.Setoids.TwoFibreProduct.apex F₁ F₂).p := sorry

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
