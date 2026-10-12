/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hausdorff Sober Spaces

Convenient sober-space consequences of Hausdorff separation.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Example 5.8.13: every Hausdorff space is sober, expressed by `T0Space` and `QuasiSober`. -/
@[stacks 004Y "Hausdorff spaces are sober"]
theorem T2Space.sober [T2Space X] : T0Space X ∧ QuasiSober X := by
  exact ⟨inferInstance, inferInstance⟩
