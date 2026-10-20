/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.EulerPoincare.Field
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.26.4: every Euler-Poincaré function on finite modules over a field is determined
by its value on the field. -/
@[stacks 02E2] #check (Module.EulerPoincareFunction.eq_ofInt :
  {k : Type u} → [Field k] →
    (φ : Module.EulerPoincareFunction.{u, u} k) →
      φ = Module.EulerPoincareFunction.ofInt k (Module.EulerPoincareFunction.eval φ k))
