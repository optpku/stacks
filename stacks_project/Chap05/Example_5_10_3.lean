/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.KrullDimension.Hausdorff
public import Mathlib.Analysis.InnerProductSpace.PiL2
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

/-!
# Example 5.10.3

The Hausdorff zero-dimensionality theorem is reusable topology API. The
Euclidean statement is its source-specific specialization.
-/

/- The reusable Hausdorff theorem is the proof-level core. -/
#check @topologicalKrullDim_eq_zero_of_nonempty_t2

/- Example 5.10.3: the topological Krull dimension of `EuclideanSpace ℝ (Fin n)` is zero. -/
@[stacks 0056]
#check fun n : ℕ ↦
  topologicalKrullDim_eq_zero_of_nonempty_t2 (X := EuclideanSpace ℝ (Fin n))
