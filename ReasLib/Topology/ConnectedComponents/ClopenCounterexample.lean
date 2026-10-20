/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A Clopen-Neighborhood Counterexample

This explicit space shows that a connected component need not equal the
intersection of its clopen neighborhoods without additional hypotheses.
-/

@[expose] public section

namespace Topology.ConnectedComponents.ClopenCounterexample

open Set

/-- Remark 5.7.4: the points of the explicit counterexample space. -/
@[stacks 0FIY]
inductive Point where
  /-- The distinguished point whose connected component is computed. -/
  | x
  /-- The second point in every clopen neighborhood of `x`. -/
  | y
  /-- An isolated tail point. -/
  | z (n : ℕ)
deriving DecidableEq

open Point

/-- The singleton basic open containing only `z n`. -/
@[stacks 0FIY]
def zSingleton (n : ℕ) : Set Point := {z n}

/-- The tail of all points `z m` with `m ≥ n`. -/
@[stacks 0FIY]
def zTail (n : ℕ) : Set Point := range fun m ↦ z (n + m)

/-- The basic open containing `x` and the tail beginning at `n`. -/
@[stacks 0FIY]
def xTail (n : ℕ) : Set Point := insert x (zTail n)

/-- The basic open containing `y` and the tail beginning at `n`. -/
@[stacks 0FIY]
def yTail (n : ℕ) : Set Point := insert y (zTail n)

/-- The generated topology on the counterexample point set. -/
@[stacks 0FIY]
instance : TopologicalSpace Point :=
  TopologicalSpace.generateFrom (range zSingleton ∪ range xTail ∪ range yTail)

/-- Remark 5.7.4 (2): the connected component of `x` is its singleton. -/
@[stacks 0FIY "the connected component of x in the explicit space"]
theorem connectedComponent_x :
    connectedComponent x = ({x} : Set Point) := sorry

/-- Remark 5.7.4 (3): the intersection of all clopen neighborhoods of `x` is
the two-point subset `{x, y}`. -/
@[stacks 0FIY "the clopen-neighborhood intersection of x in the explicit space"]
theorem iInter_isClopen_x :
    (⋂ Z : {Z : Set Point // IsClopen Z ∧ x ∈ Z}, (Z : Set Point)) =
      ({x, y} : Set Point) := sorry

/-- Remark 5.7.4 (4): the canonical connected-component inclusion is strict
in this explicit space. -/
@[stacks 0FIY "strictness of the clopen-neighborhood inclusion"]
theorem connectedComponent_x_ssubset_iInter_isClopen :
    connectedComponent x ⊂ ⋂ Z : {Z : Set Point // IsClopen Z ∧ x ∈ Z},
      (Z : Set Point) := sorry

end Topology.ConnectedComponents.ClopenCounterexample
