/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.Tactic.CrossRefAttribute

/-!
# Concrete linear actions

Elementwise API for actions on bundled modules.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Action.ModuleCat

variable (R : Type u) [Ring R]
variable (G : Type v) [Monoid G]

/-- The canonical elementwise action underlying a bundled action on an `R`-module. -/
@[stacks 04JF "module action on elements"]
instance actionMulAction (X : Action (ModuleCat.{max u v} R) G) : MulAction G X.V :=
  _root_.Action.instMulAction X

end CategoryTheory.Action.ModuleCat
